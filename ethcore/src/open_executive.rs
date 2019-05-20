// Copyright 2015-2019 Parity Technologies (UK) Ltd.
// This file is part of Parity Ethereum.

// Parity Ethereum is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Parity Ethereum is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Parity Ethereum.  If not, see <http://www.gnu.org/licenses/>.

//! Transaction Execution environment.
use std::cmp;
use std::sync::Arc;
use hash::keccak;
use ethereum_types::{H256, U256, U512, Address};
use bytes::{Bytes, BytesRef};
use state::{Backend as StateBackend, Substate, CleanupMode};
use open_state::State;
use executed::ExecutionError;
use machine::EthereumMachine as Machine;
use evm::{CallType, Finalize, FinalizationResult};
use vm::{
    self, EnvInfo, CreateContractAddress, ReturnData, CleanDustMode, ActionParams,
    ActionValue, Schedule, TrapError, ResumeCall, ResumeCreate
};
use factory::VmFactory;
use open_externalities::*;
use trace::{self, Tracer, VMTracer};
use types::transaction::{Action, SignedTransaction};
use transaction_ext::Transaction;
use crossbeam;
pub use executed::{Executed, ExecutionResult};

#[cfg(debug_assertions)]
/// Roughly estimate what stack size each level of evm depth will use. (Debug build)
const STACK_SIZE_PER_DEPTH: usize = 128 * 1024;

#[cfg(not(debug_assertions))]
/// Roughly estimate what stack size each level of evm depth will use.
const STACK_SIZE_PER_DEPTH: usize = 24 * 1024;

#[cfg(debug_assertions)]
/// Entry stack overhead prior to execution. (Debug build)
const STACK_SIZE_ENTRY_OVERHEAD: usize = 100 * 1024;

#[cfg(not(debug_assertions))]
/// Entry stack overhead prior to execution.
const STACK_SIZE_ENTRY_OVERHEAD: usize = 20 * 1024;

/// Returns new address created from address, nonce, and code hash
pub fn contract_address(address_scheme: CreateContractAddress, sender: &Address, nonce: &U256, code: &[u8]) -> (Address, Option<H256>) {
    use rlp::RlpStream;

    match address_scheme {
        CreateContractAddress::FromSenderAndNonce => {
            let mut stream = RlpStream::new_list(2);
            stream.append(sender);
            stream.append(nonce);
            (From::from(keccak(stream.as_raw())), None)
        },
        CreateContractAddress::FromSenderSaltAndCodeHash(salt) => {
            let code_hash = keccak(code);
            let mut buffer = [0u8; 1 + 20 + 32 + 32];
            buffer[0] = 0xff;
            &mut buffer[1..(1+20)].copy_from_slice(&sender[..]);
            &mut buffer[(1+20)..(1+20+32)].copy_from_slice(&salt[..]);
            &mut buffer[(1+20+32)..].copy_from_slice(&code_hash[..]);
            (From::from(keccak(&buffer[..])), Some(code_hash))
        },
        CreateContractAddress::FromSenderAndCodeHash => {
            let code_hash = keccak(code);
            let mut buffer = [0u8; 20 + 32];
            &mut buffer[..20].copy_from_slice(&sender[..]);
            &mut buffer[20..].copy_from_slice(&code_hash[..]);
            (From::from(keccak(&buffer[..])), Some(code_hash))
        },
    }
}

/// Convert a finalization result into a VM message call result.
pub fn into_message_call_result(result: vm::Result<FinalizationResult>) -> vm::MessageCallResult {
    match result {
        Ok(FinalizationResult { gas_left, return_data, apply_state: true }) => vm::MessageCallResult::Success(gas_left, return_data),
        Ok(FinalizationResult { gas_left, return_data, apply_state: false }) => vm::MessageCallResult::Reverted(gas_left, return_data),
        _ => vm::MessageCallResult::Failed
    }
}

/// Convert a finalization result into a VM contract create result.
pub fn into_contract_create_result(result: vm::Result<FinalizationResult>, address: &Address, substate: &mut Substate) -> vm::ContractCreateResult {
    match result {
        Ok(FinalizationResult { gas_left, apply_state: true, .. }) => {
            substate.contracts_created.push(address.clone());
            vm::ContractCreateResult::Created(address.clone(), gas_left)
        },
        Ok(FinalizationResult { gas_left, apply_state: false, return_data }) => {
            vm::ContractCreateResult::Reverted(gas_left, return_data)
        },
        _ => vm::ContractCreateResult::Failed,
    }
}

/// Transaction execution options.
#[derive(Copy, Clone, PartialEq)]
pub struct TransactOptions<T, V> {
    /// Enable call tracing.
    pub tracer: T,
    /// Enable VM tracing.
    pub vm_tracer: V,
    /// Check transaction nonce before execution.
    pub check_nonce: bool,
    /// Records the output from init contract calls.
    pub output_from_init_contract: bool,
}

impl<T, V> TransactOptions<T, V> {
    /// Create new `TransactOptions` with given tracer and VM tracer.
    pub fn new(tracer: T, vm_tracer: V) -> Self {
        TransactOptions {
            tracer,
            vm_tracer,
            check_nonce: true,
            output_from_init_contract: false,
        }
    }

    /// Disables the nonce check
    pub fn dont_check_nonce(mut self) -> Self {
        self.check_nonce = false;
        self
    }

    /// Saves the output from contract creation.
    pub fn save_output_from_contract(mut self) -> Self {
        self.output_from_init_contract = true;
        self
    }
}

impl TransactOptions<trace::ExecutiveTracer, trace::ExecutiveVMTracer> {
    /// Creates new `TransactOptions` with default tracing and VM tracing.
    pub fn with_tracing_and_vm_tracing() -> Self {
        TransactOptions {
            tracer: trace::ExecutiveTracer::default(),
            vm_tracer: trace::ExecutiveVMTracer::toplevel(),
            check_nonce: true,
            output_from_init_contract: false,
        }
    }
}

impl TransactOptions<trace::ExecutiveTracer, trace::NoopVMTracer> {
    /// Creates new `TransactOptions` with default tracing and no VM tracing.
    pub fn with_tracing() -> Self {
        TransactOptions {
            tracer: trace::ExecutiveTracer::default(),
            vm_tracer: trace::NoopVMTracer,
            check_nonce: true,
            output_from_init_contract: false,
        }
    }
}

impl TransactOptions<trace::NoopTracer, trace::ExecutiveVMTracer> {
    /// Creates new `TransactOptions` with no tracing and default VM tracing.
    pub fn with_vm_tracing() -> Self {
        TransactOptions {
            tracer: trace::NoopTracer,
            vm_tracer: trace::ExecutiveVMTracer::toplevel(),
            check_nonce: true,
            output_from_init_contract: false,
        }
    }
}

impl TransactOptions<trace::NoopTracer, trace::NoopVMTracer> {
    /// Creates new `TransactOptions` without any tracing.
    pub fn with_no_tracing() -> Self {
        TransactOptions {
            tracer: trace::NoopTracer,
            vm_tracer: trace::NoopVMTracer,
            check_nonce: true,
            output_from_init_contract: false,
        }
    }
}

/// Trap result returned by executive.
pub type ExecutiveTrapResult<'a, T> = vm::TrapResult<T, CallCreateExecutive<'a>, CallCreateExecutive<'a>>;
/// Trap error for executive.
pub type ExecutiveTrapError<'a> = vm::TrapError<CallCreateExecutive<'a>, CallCreateExecutive<'a>>;

enum CallCreateExecutiveKind {
    Transfer(ActionParams),
    CallBuiltin(ActionParams),
    ExecCall(ActionParams, Substate),
    ExecCreate(ActionParams, Substate),
    ResumeCall(OriginInfo, Box<ResumeCall>, Substate),
    ResumeCreate(OriginInfo, Box<ResumeCreate>, Substate),
}

/// Executive for a raw call/create action.
pub struct CallCreateExecutive<'a> {
    info: &'a EnvInfo,
    machine: &'a Machine,
    schedule: &'a Schedule,
    factory: &'a VmFactory,
    depth: usize,
    stack_depth: usize,
    static_flag: bool,
    is_create: bool,
    gas: U256,
    kind: CallCreateExecutiveKind,
}

impl<'a> CallCreateExecutive<'a> {
    /// Create a new call executive using raw data.
    pub fn new_call_raw(params: ActionParams, info: &'a EnvInfo, machine: &'a Machine, schedule: &'a Schedule, factory: &'a VmFactory, depth: usize, stack_depth: usize, parent_static_flag: bool) -> Self {
        trace!("Executive::call(params={:?}) self.env_info={:?}, parent_static={}", params, info, parent_static_flag);

        let gas = params.gas;
        let static_flag = parent_static_flag || params.call_type == CallType::StaticCall;

        // if destination is builtin, try to execute it
        let kind = if let Some(builtin) = machine.builtin(&params.code_address, info.number) {
            // Engines aren't supposed to return builtins until activation, but
            // prefer to fail rather than silently break consensus.
            if !builtin.is_active(info.number) {
                panic!("Consensus failure: engine implementation prematurely enabled built-in at {}", params.code_address);
            }

            CallCreateExecutiveKind::CallBuiltin(params)
        } else {
            if params.code.is_some() {
                CallCreateExecutiveKind::ExecCall(params, Substate::new())
            } else {
                CallCreateExecutiveKind::Transfer(params)
            }
        };

        Self {
            info, machine, schedule, factory, depth, stack_depth, static_flag, kind, gas,
            is_create: false,
        }
    }

    /// Create a new create executive using raw data.
    pub fn new_create_raw(params: ActionParams, info: &'a EnvInfo, machine: &'a Machine, schedule: &'a Schedule, factory: &'a VmFactory, depth: usize, stack_depth: usize, static_flag: bool) -> Self {
        trace!("Executive::create(params={:?}) self.env_info={:?}, static={}", params, info, static_flag);

        let gas = params.gas;

        let kind = CallCreateExecutiveKind::ExecCreate(params, Substate::new());

        Self {
            info, machine, schedule, factory, depth, stack_depth, static_flag, kind, gas,
            is_create: true,
        }
    }

    /// If this executive contains an unconfirmed substate, returns a mutable reference to it.
    pub fn unconfirmed_substate(&mut self) -> Option<&mut Substate> {
        match self.kind {
            CallCreateExecutiveKind::ExecCall(_, ref mut unsub) => Some(unsub),
            CallCreateExecutiveKind::ExecCreate(_, ref mut unsub) => Some(unsub),
            CallCreateExecutiveKind::ResumeCreate(_, _, ref mut unsub) => Some(unsub),
            CallCreateExecutiveKind::ResumeCall(_, _, ref mut unsub) => Some(unsub),
            CallCreateExecutiveKind::Transfer(..) | CallCreateExecutiveKind::CallBuiltin(..) => None,
        }
    }

    fn check_static_flag(params: &ActionParams, static_flag: bool, is_create: bool) -> vm::Result<()> {
        if is_create {
            if static_flag {
                return Err(vm::Error::MutableCallInStaticContext);
            }
        } else {
            if (static_flag &&
                (params.call_type == CallType::StaticCall || params.call_type == CallType::Call)) &&
                params.value.value() > U256::zero()
                {
                    return Err(vm::Error::MutableCallInStaticContext);
                }
        }

        Ok(())
    }

    fn check_eip684<B: 'a + StateBackend>(params: &ActionParams, state: &State<B>) -> vm::Result<()> {
        if state.exists_and_has_code_or_nonce(&params.address)? {
            return Err(vm::Error::OutOfGas);
        }

        Ok(())
    }

    fn transfer_exec_balance<B: 'a + StateBackend>(params: &ActionParams, schedule: &Schedule, state: &mut State<B>, substate: &mut Substate) -> vm::Result<()> {
        if let ActionValue::Transfer(val) = params.value {
            state.transfer_balance(&params.sender, &params.address, &val, substate.to_cleanup_mode(&schedule))?;
        }

        Ok(())
    }

    fn transfer_exec_balance_and_init_contract<B: 'a + StateBackend>(params: &ActionParams, schedule: &Schedule, state: &mut State<B>, substate: &mut Substate) -> vm::Result<()> {
        let nonce_offset = if schedule.no_empty {1} else {0}.into();
        let prev_bal = state.balance(&params.address)?;
        if let ActionValue::Transfer(val) = params.value {
            state.sub_balance(&params.sender, &val, &mut substate.to_cleanup_mode(&schedule))?;
            state.new_contract(&params.address, val.saturating_add(prev_bal), nonce_offset)?;
        } else {
            state.new_contract(&params.address, prev_bal, nonce_offset)?;
        }

        Ok(())
    }

    fn enact_result<B: 'a + StateBackend>(result: &vm::Result<FinalizationResult>, state: &mut State<B>, substate: &mut Substate, un_substate: Substate) {
        match *result {
            Err(vm::Error::OutOfGas)
                | Err(vm::Error::BadJumpDestination {..})
                | Err(vm::Error::BadInstruction {.. })
                | Err(vm::Error::StackUnderflow {..})
                | Err(vm::Error::BuiltIn {..})
                | Err(vm::Error::Wasm {..})
                | Err(vm::Error::OutOfStack {..})
                | Err(vm::Error::MutableCallInStaticContext)
                | Err(vm::Error::OutOfBounds)
                | Err(vm::Error::Reverted)
                | Ok(FinalizationResult { apply_state: false, .. }) => {
                    state.revert_to_checkpoint();
                },
                Ok(_) | Err(vm::Error::Internal(_)) => {
                    state.discard_checkpoint();
                    substate.accrue(un_substate);
                }
        }
    }

    /// Creates `Externalities` from `Executive`.
    fn as_externalities<'any, B: 'any + StateBackend, T, V>(
        state: &'any mut State<B>,
        info: &'any EnvInfo,
        machine: &'any Machine,
        schedule: &'any Schedule,
        depth: usize,
        stack_depth: usize,
        static_flag: bool,
        origin_info: &'any OriginInfo,
        substate: &'any mut Substate,
        output: OutputPolicy,
        tracer: &'any mut T,
        vm_tracer: &'any mut V,
        ) -> Externalities<'any, T, V, B> where T: Tracer, V: VMTracer {
        Externalities::new(state, info, machine, schedule, depth, stack_depth, origin_info, substate, output, tracer, vm_tracer, static_flag)
    }

    /// Execute the executive. If a sub-call/create action is required, a resume trap error is returned. The caller is
    /// then expected to call `resume_call` or `resume_create` to continue the execution.
    ///
    /// Current-level tracing is expected to be handled by caller.
    pub fn exec<B: 'a + StateBackend, T: Tracer, V: VMTracer>(mut self, state: &mut State<B>, substate: &mut Substate, tracer: &mut T, vm_tracer: &mut V) -> ExecutiveTrapResult<'a, FinalizationResult> {
        match self.kind {
            CallCreateExecutiveKind::Transfer(ref params) => {
                assert!(!self.is_create);

                let mut inner = || {
                    Self::check_static_flag(params, self.static_flag, self.is_create)?;
                    Self::transfer_exec_balance(params, self.schedule, state, substate)?;

                    Ok(FinalizationResult {
                        gas_left: params.gas,
                        return_data: ReturnData::empty(),
                        apply_state: true,
                    })
                };

                Ok(inner())
            },
            CallCreateExecutiveKind::CallBuiltin(ref params) => {
                assert!(!self.is_create);

                let mut inner = || {
                    let builtin = self.machine.builtin(&params.code_address, self.info.number).expect("Builtin is_some is checked when creating this kind in new_call_raw; qed");

                    Self::check_static_flag(&params, self.static_flag, self.is_create)?;
                    state.checkpoint();
                    Self::transfer_exec_balance(&params, self.schedule, state, substate)?;

                    let default = [];
                    let data = if let Some(ref d) = params.data { d as &[u8] } else { &default as &[u8] };

                    let cost = builtin.cost(data);
                    if cost <= params.gas {
                        let mut builtin_out_buffer = Vec::new();
                        let result = {
                            let mut builtin_output = BytesRef::Flexible(&mut builtin_out_buffer);
                            builtin.execute(data, &mut builtin_output)
                        };
                        if let Err(e) = result {
                            state.revert_to_checkpoint();

                            Err(e.into())
                        } else {
                            state.discard_checkpoint();

                            let out_len = builtin_out_buffer.len();
                            Ok(FinalizationResult {
                                gas_left: params.gas - cost,
                                return_data: ReturnData::new(builtin_out_buffer, 0, out_len),
                                apply_state: true,
                            })
                        }
                    } else {
                        // just drain the whole gas
                        state.revert_to_checkpoint();

                        Err(vm::Error::OutOfGas)
                    }
                };

                Ok(inner())
            },
            CallCreateExecutiveKind::ExecCall(params, mut unconfirmed_substate) => {
                assert!(!self.is_create);

                {
                    let static_flag = self.static_flag;
                    let is_create = self.is_create;
                    let schedule = self.schedule;

                    let mut pre_inner = || {
                        Self::check_static_flag(&params, static_flag, is_create)?;
                        state.checkpoint();
                        Self::transfer_exec_balance(&params, schedule, state, substate)?;
                        Ok(())
                    };

                    match pre_inner() {
                        Ok(()) => (),
                        Err(err) => return Ok(Err(err)),
                    }
                }

                let origin_info = OriginInfo::from(&params);
                let exec = self.factory.create(params, self.schedule, self.depth);

                let out = {
                    let mut ext = Self::as_externalities(state, self.info, self.machine, self.schedule, self.depth, self.stack_depth, self.static_flag, &origin_info, &mut unconfirmed_substate, OutputPolicy::Return, tracer, vm_tracer);
                    match exec.exec(&mut ext) {
                        Ok(val) => Ok(val.finalize(ext)),
                        Err(err) => Err(err),
                    }
                };

                let res = match out {
                    Ok(val) => val,
                    Err(TrapError::Call(subparams, resume)) => {
                        self.kind = CallCreateExecutiveKind::ResumeCall(origin_info, resume, unconfirmed_substate);
                        return Err(TrapError::Call(subparams, self));
                    },
                    Err(TrapError::Create(subparams, address, resume)) => {
                        self.kind = CallCreateExecutiveKind::ResumeCreate(origin_info, resume, unconfirmed_substate);
                        return Err(TrapError::Create(subparams, address, self));
                    },
                };

                Self::enact_result(&res, state, substate, unconfirmed_substate);
                Ok(res)
            },
            CallCreateExecutiveKind::ExecCreate(params, mut unconfirmed_substate) => {
                assert!(self.is_create);

                {
                    let static_flag = self.static_flag;
                    let is_create = self.is_create;
                    let schedule = self.schedule;

                    let mut pre_inner = || {
                        Self::check_eip684(&params, state)?;
                        Self::check_static_flag(&params, static_flag, is_create)?;
                        state.checkpoint();
                        Self::transfer_exec_balance_and_init_contract(&params, schedule, state, substate)?;
                        Ok(())
                    };

                    match pre_inner() {
                        Ok(()) => (),
                        Err(err) => return Ok(Err(err)),
                    }
                }

                let origin_info = OriginInfo::from(&params);
                let exec = self.factory.create(params, self.schedule, self.depth);

                let out = {
                    let mut ext = Self::as_externalities(state, self.info, self.machine, self.schedule, self.depth, self.stack_depth, self.static_flag, &origin_info, &mut unconfirmed_substate, OutputPolicy::InitContract, tracer, vm_tracer);
                    match exec.exec(&mut ext) {
                        Ok(val) => Ok(val.finalize(ext)),
                        Err(err) => Err(err),
                    }
                };

                let res = match out {
                    Ok(val) => val,
                    Err(TrapError::Call(subparams, resume)) => {
                        self.kind = CallCreateExecutiveKind::ResumeCall(origin_info, resume, unconfirmed_substate);
                        return Err(TrapError::Call(subparams, self));
                    },
                    Err(TrapError::Create(subparams, address, resume)) => {
                        self.kind = CallCreateExecutiveKind::ResumeCreate(origin_info, resume, unconfirmed_substate);
                        return Err(TrapError::Create(subparams, address, self));
                    },
                };

                Self::enact_result(&res, state, substate, unconfirmed_substate);
                Ok(res)
            },
            CallCreateExecutiveKind::ResumeCall(..) | CallCreateExecutiveKind::ResumeCreate(..) => panic!("This executive has already been executed once."),
        }
    }

    /// Resume execution from a call trap previsouly trapped by `exec`.
    ///
    /// Current-level tracing is expected to be handled by caller.
    pub fn resume_call<B: 'a + StateBackend, T: Tracer, V: VMTracer>(mut self, result: vm::MessageCallResult, state: &mut State<B>, substate: &mut Substate, tracer: &mut T, vm_tracer: &mut V) -> ExecutiveTrapResult<'a, FinalizationResult> {
        match self.kind {
            CallCreateExecutiveKind::ResumeCall(origin_info, resume, mut unconfirmed_substate) => {
                let out = {
                    let exec = resume.resume_call(result);

                    let mut ext = Self::as_externalities(state, self.info, self.machine, self.schedule, self.depth, self.stack_depth, self.static_flag, &origin_info, &mut unconfirmed_substate, if self.is_create { OutputPolicy::InitContract } else { OutputPolicy::Return }, tracer, vm_tracer);
                    match exec.exec(&mut ext) {
                        Ok(val) => Ok(val.finalize(ext)),
                        Err(err) => Err(err),
                    }
                };

                let res = match out {
                    Ok(val) => val,
                    Err(TrapError::Call(subparams, resume)) => {
                        self.kind = CallCreateExecutiveKind::ResumeCall(origin_info, resume, unconfirmed_substate);
                        return Err(TrapError::Call(subparams, self));
                    },
                    Err(TrapError::Create(subparams, address, resume)) => {
                        self.kind = CallCreateExecutiveKind::ResumeCreate(origin_info, resume, unconfirmed_substate);
                        return Err(TrapError::Create(subparams, address, self));
                    },
                };

                Self::enact_result(&res, state, substate, unconfirmed_substate);
                Ok(res)
            },
            CallCreateExecutiveKind::ResumeCreate(..) =>
                panic!("Resumable as create, but called resume_call"),
                CallCreateExecutiveKind::Transfer(..) | CallCreateExecutiveKind::CallBuiltin(..) |
                    CallCreateExecutiveKind::ExecCall(..) | CallCreateExecutiveKind::ExecCreate(..) =>
                    panic!("Not resumable"),
        }
    }

    /// Resume execution from a create trap previsouly trapped by `exec`.
    ///
    /// Current-level tracing is expected to be handled by caller.
    pub fn resume_create<B: 'a + StateBackend, T: Tracer, V: VMTracer>(mut self, result: vm::ContractCreateResult, state: &mut State<B>, substate: &mut Substate, tracer: &mut T, vm_tracer: &mut V) -> ExecutiveTrapResult<'a, FinalizationResult> {
        match self.kind {
            CallCreateExecutiveKind::ResumeCreate(origin_info, resume, mut unconfirmed_substate) => {
                let out = {
                    let exec = resume.resume_create(result);

                    let mut ext = Self::as_externalities(state, self.info, self.machine, self.schedule, self.depth, self.stack_depth, self.static_flag, &origin_info, &mut unconfirmed_substate, if self.is_create { OutputPolicy::InitContract } else { OutputPolicy::Return }, tracer, vm_tracer);
                    match exec.exec(&mut ext) {
                        Ok(val) => Ok(val.finalize(ext)),
                        Err(err) => Err(err),
                    }
                };

                let res = match out {
                    Ok(val) => val,
                    Err(TrapError::Call(subparams, resume)) => {
                        self.kind = CallCreateExecutiveKind::ResumeCall(origin_info, resume, unconfirmed_substate);
                        return Err(TrapError::Call(subparams, self));
                    },
                    Err(TrapError::Create(subparams, address, resume)) => {
                        self.kind = CallCreateExecutiveKind::ResumeCreate(origin_info, resume, unconfirmed_substate);
                        return Err(TrapError::Create(subparams, address, self));
                    },
                };

                Self::enact_result(&res, state, substate, unconfirmed_substate);
                Ok(res)
            },
            CallCreateExecutiveKind::ResumeCall(..) =>
                panic!("Resumable as call, but called resume_create"),
                CallCreateExecutiveKind::Transfer(..) | CallCreateExecutiveKind::CallBuiltin(..) |
                    CallCreateExecutiveKind::ExecCall(..) | CallCreateExecutiveKind::ExecCreate(..) =>
                    panic!("Not resumable"),
        }
    }

    /// Execute and consume the current executive. This function handles resume traps and sub-level tracing. The caller is expected to handle current-level tracing.
    pub fn consume<B: 'a + StateBackend, T: Tracer, V: VMTracer>(self, state: &mut State<B>, top_substate: &mut Substate, tracer: &mut T, vm_tracer: &mut V) -> vm::Result<FinalizationResult> {
        let mut last_res = Some((false, self.gas, self.exec(state, top_substate, tracer, vm_tracer)));

        let mut callstack: Vec<(Option<Address>, CallCreateExecutive<'a>)> = Vec::new();
        loop {
            match last_res {
                None => {
                    match callstack.pop() {
                        Some((_, exec)) => {
                            let second_last = callstack.last_mut();
                            let parent_substate = match second_last {
                                Some((_, ref mut second_last)) => second_last.unconfirmed_substate().expect("Current stack value is created from second last item; second last item must be call or create; qed"),
                                None => top_substate,
                            };

                            last_res = Some((exec.is_create, exec.gas, exec.exec(state, parent_substate, tracer, vm_tracer)));
                        },
                        None => panic!("When callstack only had one item and it was executed, this function would return; callstack never reaches zero item; qed"),
                    }
                },
                Some((is_create, gas, Ok(val))) => {
                    let current = callstack.pop();

                    match current {
                        Some((address, mut exec)) => {
                            if is_create {
                                let address = address.expect("If the last executed status was from a create executive, then the destination address was pushed to the callstack; address is_some if it is_create; qed");

                                match val {
                                    Ok(ref val) if val.apply_state => {
                                        tracer.done_trace_create(
                                            gas - val.gas_left,
                                            &val.return_data,
                                            address
                                        );
                                    },
                                    Ok(_) => {
                                        tracer.done_trace_failed(&vm::Error::Reverted);
                                    },
                                    Err(ref err) => {
                                        tracer.done_trace_failed(err);
                                    },
                                }

                                vm_tracer.done_subtrace();

                                let second_last = callstack.last_mut();
                                let parent_substate = match second_last {
                                    Some((_, ref mut second_last)) => second_last.unconfirmed_substate().expect("Current stack value is created from second last item; second last item must be call or create; qed"),
                                    None => top_substate,
                                };

                                let contract_create_result = into_contract_create_result(val, &address, exec.unconfirmed_substate().expect("Executive is resumed from a create; it has an unconfirmed substate; qed"));
                                last_res = Some((exec.is_create, exec.gas, exec.resume_create(
                                            contract_create_result,
                                            state,
                                            parent_substate,
                                            tracer,
                                            vm_tracer
                                )));
                            } else {
                                match val {
                                    Ok(ref val) if val.apply_state => {
                                        tracer.done_trace_call(
                                            gas - val.gas_left,
                                            &val.return_data,
                                            );
                                    },
                                    Ok(_) => {
                                        tracer.done_trace_failed(&vm::Error::Reverted);
                                    },
                                    Err(ref err) => {
                                        tracer.done_trace_failed(err);
                                    },
                                }

                                vm_tracer.done_subtrace();

                                let second_last = callstack.last_mut();
                                let parent_substate = match second_last {
                                    Some((_, ref mut second_last)) => second_last.unconfirmed_substate().expect("Current stack value is created from second last item; second last item must be call or create; qed"),
                                    None => top_substate,
                                };

                                last_res = Some((exec.is_create, exec.gas, exec.resume_call(
                                            into_message_call_result(val),
                                            state,
                                            parent_substate,
                                            tracer,
                                            vm_tracer
                                )));
                            }
                        },
                        None => return val,
                    }
                },
                Some((_, _, Err(TrapError::Call(subparams, resume)))) => {
                    tracer.prepare_trace_call(&subparams, resume.depth + 1, resume.machine.builtin(&subparams.address, resume.info.number).is_some());
                    vm_tracer.prepare_subtrace(subparams.code.as_ref().map_or_else(|| &[] as &[u8], |d| &*d as &[u8]));

                    let sub_exec = CallCreateExecutive::new_call_raw(
                        subparams,
                        resume.info,
                        resume.machine,
                        resume.schedule,
                        resume.factory,
                        resume.depth + 1,
                        resume.stack_depth,
                        resume.static_flag,
                        );

                    callstack.push((None, resume));
                    callstack.push((None, sub_exec));
                    last_res = None;
                },
                Some((_, _, Err(TrapError::Create(subparams, address, resume)))) => {
                    tracer.prepare_trace_create(&subparams);
                    vm_tracer.prepare_subtrace(subparams.code.as_ref().map_or_else(|| &[] as &[u8], |d| &*d as &[u8]));

                    let sub_exec = CallCreateExecutive::new_create_raw(
                        subparams,
                        resume.info,
                        resume.machine,
                        resume.schedule,
                        resume.factory,
                        resume.depth + 1,
                        resume.stack_depth,
                        resume.static_flag
                    );

                    callstack.push((Some(address), resume));
                    callstack.push((None, sub_exec));
                    last_res = None;
                },
            }
        }
    }
}

/// Transaction executor.
pub struct Executive<'a, B: 'a> {
    state: &'a mut State<B>,
    info: &'a EnvInfo,
    machine: &'a Machine,
    schedule: &'a Schedule,
    depth: usize,
    static_flag: bool,
}

impl<'a, B: 'a + StateBackend> Executive<'a, B> {
    /// Basic constructor.
    pub fn new(state: &'a mut State<B>, info: &'a EnvInfo, machine: &'a Machine, schedule: &'a Schedule) -> Self {
        Executive {
            state: state,
            info: info,
            machine: machine,
            schedule: schedule,
            depth: 0,
            static_flag: false,
        }
    }

    /// Populates executive from parent properties. Increments executive depth.
    pub fn from_parent(state: &'a mut State<B>, info: &'a EnvInfo, machine: &'a Machine, schedule: &'a Schedule, parent_depth: usize, static_flag: bool) -> Self {
        Executive {
            state: state,
            info: info,
            machine: machine,
            schedule: schedule,
            depth: parent_depth + 1,
            static_flag: static_flag,
        }
    }

    /// This function should be used to execute transaction.
    pub fn transact<T, V>(&'a mut self, t: &SignedTransaction, options: TransactOptions<T, V>)
        -> Result<Executed<T::Output, V::Output>, ExecutionError> where T: Tracer, V: VMTracer,
    {
        self.transact_with_tracer(t, options.check_nonce, options.output_from_init_contract, options.tracer, options.vm_tracer)
    }

    /// Execute a transaction in a "virtual" context.
    /// This will ensure the caller has enough balance to execute the desired transaction.
    /// Used for extra-block executions for things like consensus contracts and RPCs
    pub fn transact_virtual<T, V>(&'a mut self, t: &SignedTransaction, options: TransactOptions<T, V>)
        -> Result<Executed<T::Output, V::Output>, ExecutionError> where T: Tracer, V: VMTracer,
    {
        let sender = t.sender();
        let balance = self.state.balance(&sender)?;
        let needed_balance = t.value.saturating_add(t.gas.saturating_mul(t.gas_price));
        if balance < needed_balance {
            // give the sender a sufficient balance
            self.state.add_balance(&sender, &(needed_balance - balance), CleanupMode::NoEmpty)?;
        }

        self.transact(t, options)
    }

    /// Execute transaction/call with tracing enabled
    fn transact_with_tracer<T, V>(
        &'a mut self,
        t: &SignedTransaction,
        check_nonce: bool,
        output_from_create: bool,
        mut tracer: T,
        mut vm_tracer: V
    ) -> Result<Executed<T::Output, V::Output>, ExecutionError> where T: Tracer, V: VMTracer {
        let sender = t.sender();
        let nonce = self.state.nonce(&sender)?;

        let schedule = self.schedule;
        let base_gas_required = U256::from(t.gas_required(&schedule));

        if t.gas < base_gas_required {
            return Err(ExecutionError::NotEnoughBaseGas { required: base_gas_required, got: t.gas });
        }

        if !t.is_unsigned() && check_nonce && schedule.kill_dust != CleanDustMode::Off && !self.state.exists(&sender)? {
            return Err(ExecutionError::SenderMustExist);
        }

        let init_gas = t.gas - base_gas_required;

        // validate transaction nonce
        if check_nonce && t.nonce != nonce {
            return Err(ExecutionError::InvalidNonce { expected: nonce, got: t.nonce });
        }

        // validate if transaction fits into given block
        if self.info.gas_used + t.gas > self.info.gas_limit {
            return Err(ExecutionError::BlockGasLimitReached {
                gas_limit: self.info.gas_limit,
                gas_used: self.info.gas_used,
                gas: t.gas
            });
        }

        // TODO: we might need bigints here, or at least check overflows.
        let balance = self.state.balance(&sender)?;
        let gas_cost = t.gas.full_mul(t.gas_price);
        let total_cost = U512::from(t.value) + gas_cost;

        // avoid unaffordable transactions
        let balance512 = U512::from(balance);
        if balance512 < total_cost {
            return Err(ExecutionError::NotEnoughCash { required: total_cost, got: balance512 });
        }

        let mut substate = Substate::new();

        // NOTE: there can be no invalid transactions from this point.
        if !schedule.keep_unsigned_nonce || !t.is_unsigned() {
            self.state.inc_nonce(&sender)?;
        }
        self.state.sub_balance(&sender, &U256::from(gas_cost), &mut substate.to_cleanup_mode(&schedule))?;

        let (result, output) = match t.action {
            Action::Create => {
                let (new_address, code_hash) = contract_address(self.machine.create_address_scheme(self.info.number), &sender, &nonce, &t.data);
                let params = ActionParams {
                    code_address: new_address.clone(),
                    code_hash: code_hash,
                    address: new_address,
                    sender: sender.clone(),
                    origin: sender.clone(),
                    gas: init_gas,
                    gas_price: t.gas_price,
                    value: ActionValue::Transfer(t.value),
                    code: Some(Arc::new(t.data.clone())),
                    data: None,
                    call_type: CallType::None,
                    params_type: vm::ParamsType::Embedded,
                };
                let res = self.create(params, &mut substate, &mut tracer, &mut vm_tracer);
                let out = match &res {
                    Ok(res) if output_from_create => res.return_data.to_vec(),
                    _ => Vec::new(),
                };
                (res, out)
            },
            Action::Call(ref address) => {
                let params = ActionParams {
                    code_address: address.clone(),
                    address: address.clone(),
                    sender: sender.clone(),
                    origin: sender.clone(),
                    gas: init_gas,
                    gas_price: t.gas_price,
                    value: ActionValue::Transfer(t.value),
                    code: self.state.code(address)?,
                    code_hash: self.state.code_hash(address)?,
                    data: Some(t.data.clone()),
                    call_type: CallType::Call,
                    params_type: vm::ParamsType::Separate,
                };
                let res = self.call(params, &mut substate, &mut tracer, &mut vm_tracer);
                let out = match &res {
                    Ok(res) => res.return_data.to_vec(),
                    _ => Vec::new(),
                };
                (res, out)
            }
        };

        // finalize here!
        Ok(self.finalize(t, substate, result, output, tracer.drain(), vm_tracer.drain())?)
    }

    /// Calls contract function with given contract params and stack depth.
    /// NOTE. It does not finalize the transaction (doesn't do refunds, nor suicides).
    /// Modifies the substate and the output.
    /// Returns either gas_left or `vm::Error`.
    pub fn call_with_stack_depth<T, V>(
        &mut self,
        params: ActionParams,
        substate: &mut Substate,
        stack_depth: usize,
        tracer: &mut T,
        vm_tracer: &mut V
    ) -> vm::Result<FinalizationResult> where T: Tracer, V: VMTracer {
        tracer.prepare_trace_call(&params, self.depth, self.machine.builtin(&params.address, self.info.number).is_some());
        vm_tracer.prepare_subtrace(params.code.as_ref().map_or_else(|| &[] as &[u8], |d| &*d as &[u8]));

        let gas = params.gas;

        let vm_factory = self.state.vm_factory();
        let result = CallCreateExecutive::new_call_raw(
            params,
            self.info,
            self.machine,
            self.schedule,
            &vm_factory,
            self.depth,
            stack_depth,
            self.static_flag
        ).consume(self.state, substate, tracer, vm_tracer);

        match result {
            Ok(ref val) if val.apply_state => {
                tracer.done_trace_call(
                    gas - val.gas_left,
                    &val.return_data,
                    );
            },
            Ok(_) => {
                tracer.done_trace_failed(&vm::Error::Reverted);
            },
            Err(ref err) => {
                tracer.done_trace_failed(err);
            },
        }
        vm_tracer.done_subtrace();

        result
    }

    /// Calls contract function with given contract params, if the stack depth is above a threshold, create a new thread
    /// to execute it.
    pub fn call_with_crossbeam<T, V>(
        &mut self,
        params: ActionParams,
        substate: &mut Substate,
        stack_depth: usize,
        tracer: &mut T,
        vm_tracer: &mut V
    ) -> vm::Result<FinalizationResult> where T: Tracer, V: VMTracer {
        let local_stack_size = ::io::LOCAL_STACK_SIZE.with(|sz| sz.get());
        let depth_threshold = local_stack_size.saturating_sub(STACK_SIZE_ENTRY_OVERHEAD) / STACK_SIZE_PER_DEPTH;

        if stack_depth != depth_threshold {
            self.call_with_stack_depth(params, substate, stack_depth, tracer, vm_tracer)
        } else {
            crossbeam::scope(|scope| {
                scope.builder().stack_size(::std::cmp::max(self.schedule.max_depth.saturating_sub(depth_threshold) * STACK_SIZE_PER_DEPTH, local_stack_size)).spawn(move || {
                    self.call_with_stack_depth(params, substate, stack_depth, tracer, vm_tracer)
                }).expect("Sub-thread creation cannot fail; the host might run out of resources; qed")
            }).join().expect("Sub-thread never panics; qed")
        }
    }

    /// Calls contract function with given contract params.
    pub fn call<T, V>(
        &mut self,
        params: ActionParams,
        substate: &mut Substate,
        tracer: &mut T,
        vm_tracer: &mut V
    ) -> vm::Result<FinalizationResult> where T: Tracer, V: VMTracer {
        self.call_with_stack_depth(params, substate, 0, tracer, vm_tracer)
    }

    /// Creates contract with given contract params and stack depth.
    /// NOTE. It does not finalize the transaction (doesn't do refunds, nor suicides).
    /// Modifies the substate.
    pub fn create_with_stack_depth<T, V>(
        &mut self,
        params: ActionParams,
        substate: &mut Substate,
        stack_depth: usize,
        tracer: &mut T,
        vm_tracer: &mut V,
        ) -> vm::Result<FinalizationResult> where T: Tracer, V: VMTracer {
        tracer.prepare_trace_create(&params);
        vm_tracer.prepare_subtrace(params.code.as_ref().map_or_else(|| &[] as &[u8], |d| &*d as &[u8]));

        let address = params.address;
        let gas = params.gas;

        let vm_factory = self.state.vm_factory();
        let result = CallCreateExecutive::new_create_raw(
            params,
            self.info,
            self.machine,
            self.schedule,
            &vm_factory,
            self.depth,
            stack_depth,
            self.static_flag
        ).consume(self.state, substate, tracer, vm_tracer);

        match result {
            Ok(ref val) if val.apply_state => {
                tracer.done_trace_create(
                    gas - val.gas_left,
                    &val.return_data,
                    address,
                    );
            },
            Ok(_) => {
                tracer.done_trace_failed(&vm::Error::Reverted);
            },
            Err(ref err) => {
                tracer.done_trace_failed(err);
            },
        }
        vm_tracer.done_subtrace();

        result
    }

    /// Creates contract with given contract params, if the stack depth is above a threshold, create a new thread to
    /// execute it.
    pub fn create_with_crossbeam<T, V>(
        &mut self,
        params: ActionParams,
        substate: &mut Substate,
        stack_depth: usize,
        tracer: &mut T,
        vm_tracer: &mut V,
        ) -> vm::Result<FinalizationResult> where T: Tracer, V: VMTracer {
        let local_stack_size = ::io::LOCAL_STACK_SIZE.with(|sz| sz.get());
        let depth_threshold = local_stack_size.saturating_sub(STACK_SIZE_ENTRY_OVERHEAD) / STACK_SIZE_PER_DEPTH;

        if stack_depth != depth_threshold {
            self.create_with_stack_depth(params, substate, stack_depth, tracer, vm_tracer)
        } else {
            crossbeam::scope(|scope| {
                scope.builder().stack_size(::std::cmp::max(self.schedule.max_depth.saturating_sub(depth_threshold) * STACK_SIZE_PER_DEPTH, local_stack_size)).spawn(move || {
                    self.create_with_stack_depth(params, substate, stack_depth, tracer, vm_tracer)
                }).expect("Sub-thread creation cannot fail; the host might run out of resources; qed")
            }).join().expect("Sub-thread never panics; qed")
        }
    }

    /// Creates contract with given contract params.
    pub fn create<T, V>(
        &mut self,
        params: ActionParams,
        substate: &mut Substate,
        tracer: &mut T,
        vm_tracer: &mut V,
        ) -> vm::Result<FinalizationResult> where T: Tracer, V: VMTracer {
        self.create_with_stack_depth(params, substate, 0, tracer, vm_tracer)
    }

    /// Finalizes the transaction (does refunds and suicides).
    fn finalize<T, V>(
        &mut self,
        t: &SignedTransaction,
        mut substate: Substate,
        result: vm::Result<FinalizationResult>,
        output: Bytes,
        trace: Vec<T>,
        vm_trace: Option<V>
    ) -> Result<Executed<T, V>, ExecutionError> {
        let schedule = self.schedule;

        // refunds from SSTORE nonzero -> zero
        assert!(substate.sstore_clears_refund >= 0, "On transaction level, sstore clears refund cannot go below zero.");
        let sstore_refunds = U256::from(substate.sstore_clears_refund as u64);
        // refunds from contract suicides
        let suicide_refunds = U256::from(schedule.suicide_refund_gas) * U256::from(substate.suicides.len());
        let refunds_bound = sstore_refunds + suicide_refunds;

        // real ammount to refund
        let gas_left_prerefund = match result { Ok(FinalizationResult{ gas_left, .. }) => gas_left, _ => 0.into() };
        let refunded = cmp::min(refunds_bound, (t.gas - gas_left_prerefund) >> 1);
        let gas_left = gas_left_prerefund + refunded;

        let gas_used = t.gas.saturating_sub(gas_left);
        let (refund_value, overflow_1) = gas_left.overflowing_mul(t.gas_price);
        let (fees_value, overflow_2) = gas_used.overflowing_mul(t.gas_price);
        if overflow_1 || overflow_2 {
            return Err(ExecutionError::TransactionMalformed("U256 Overflow".to_string()));
        }


        trace!("exec::finalize: t.gas={}, sstore_refunds={}, suicide_refunds={}, refunds_bound={}, gas_left_prerefund={}, refunded={}, gas_left={}, gas_used={}, refund_value={}, fees_value={}\n",
               t.gas, sstore_refunds, suicide_refunds, refunds_bound, gas_left_prerefund, refunded, gas_left, gas_used, refund_value, fees_value);

        let sender = t.sender();
        trace!("exec::finalize: Refunding refund_value={}, sender={}\n", refund_value, sender);
        // Below: NoEmpty is safe since the sender must already be non-null to have sent this transaction
        self.state.add_balance(&sender, &refund_value, CleanupMode::NoEmpty)?;
        trace!("exec::finalize: Compensating author: fees_value={}, author={}\n", fees_value, &self.info.author);
        self.state.add_balance(&self.info.author, &fees_value, substate.to_cleanup_mode(&schedule))?;

        // perform suicides
        for address in &substate.suicides {
            self.state.kill_account(address);
        }

        // perform garbage-collection
        let min_balance = if schedule.kill_dust != CleanDustMode::Off { Some(U256::from(schedule.tx_gas).overflowing_mul(t.gas_price).0) } else { None };
        self.state.kill_garbage(&substate.touched, schedule.kill_empty, &min_balance, schedule.kill_dust == CleanDustMode::WithCodeAndStorage)?;

        match result {
            Err(vm::Error::Internal(msg)) => Err(ExecutionError::Internal(msg)),
            Err(exception) => {
                Ok(Executed {
                    exception: Some(exception),
                    gas: t.gas,
                    gas_used: t.gas,
                    refunded: U256::zero(),
                    cumulative_gas_used: self.info.gas_used + t.gas,
                    logs: vec![],
                    contracts_created: vec![],
                    output: output,
                    trace: trace,
                    vm_trace: vm_trace,
                    state_diff: None,
                })
            },
            Ok(r) => {
                Ok(Executed {
                    exception: if r.apply_state { None } else { Some(vm::Error::Reverted) },
                    gas: t.gas,
                    gas_used: gas_used,
                    refunded: refunded,
                    cumulative_gas_used: self.info.gas_used + gas_used,
                    logs: substate.logs,
                    contracts_created: substate.contracts_created,
                    output: output,
                    trace: trace,
                    vm_trace: vm_trace,
                    state_diff: None,
                })
            },
        }
    }
}
