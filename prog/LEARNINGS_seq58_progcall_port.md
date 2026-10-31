# LEARNINGS_seq58_progcall_port

Reusable proof patterns only. Greppable structured entries; evidence refs point to episodes/tool outputs/source.

## L0001 scope='C1.2' tags=state_gas,credit,CALL,safety
shape: Creation credit before abort_unuse must preserve stipend <= gasUsed
pattern: credit_new_account refunds MIN creationCost stateGasSpilled out of the whole current gasUsed, including newly charged execution cost. A nonempty-context invariant is insufficient when initial spill is unconstrained. Before reusing consume-gas credit arguments, validate the post-credit lower bound against arbitrary incoming meters.
works_when: CALL no-entry or other cross-frame refund paths; use concrete meter probes before assuming gasUsed monotonicity.
evidence:
- episode:E0004
- source:prog/vfmCallRefundProbeScript.sml

## L0002 scope='C1.2.2' tags=wordsLib,parse_opcode,parse_code,FLOOKUP
shape: Concrete opcode/parser computation leaves word comparisons or times out
pattern: Standalone theories need Libs wordsLib to register word computation. Rewrite choice-based parser with vfmOperationTheory.parse_opcode_cond_thm, then EVAL a small opcode fact. Derive singleton parse_code lookup by one unfold, opcode simplification, second unfold and FLOOKUP_UPDATE. TO_FLOOKUP alone did not simplify the update lookup.
works_when: Concrete byte-code dispatch probes importing program theories without their ML libraries.
evidence:
- tool_output:TO_seq58_progcall_port-20261030T170049Z_m0163_t001
- source:prog/vfmCallRefundProbeScript.sml

## L0003 scope='C1.2.2' tags=step,observation,state,dispatch
shape: Unfolding step expands a large concrete state under already checked step_call
pattern: First prove get_current_context s=(INL c,s) and FLOOKUP c.msgParams.parsed c.pc=SOME Call; then simp step_def/handle/bind/step_inst using these observations. The checked step_call result can close handle_step without unfolding the concrete state again.
works_when: Concrete CALL state with a checked primitive result; keeps consumer goals small.
evidence:
- tool_output:TO_seq58_progcall_port-20261030T170049Z_m0199_t001
- source:prog/vfmCallRefundProbeScript.sml

## L0004 scope='C1.3' tags=meter,spill,committed,refund,MIN
shape: Callee-local refundable backing through creation charge and credit
pattern: Use sp+committed<=gasUsed, not spill alone, for internal meter backing. Fresh initial_context satisfies it; charge_state_gas, credit_state_gas_refund, commit_state_gas, restore_state_gas and restore_state_gas_to_entry preserve it. A fresh execution charge cost with stipend<=cost survives subsequent creation charge/credit, even if creation spills. Split MIN_DEF before linear arithmetic. This concerns an executing callee only; nested gas refunds require a stronger parent margin.
works_when: Single-context primitive boundaries or no-entry CALL refund margin; not automatically internal-pop preservation.
evidence:
- episode:E0012
- source:prog/vfmCallMeterProbeScript.sml
- tool_output:TO_seq58_progcall_port-20261031T122504Z_m0321_t001

## L0005 scope='C1.3' tags=claim,spill,committed,refund,ancestor,restore
shape: Nested-frame refund budget and return preservation
pattern: Use claim=gasLimit-gasUsed+spill+committed. Each selected frame needs own spill+committed plus claims above <= gasUsed; per-frame backing alone is false under pop. Checked success absorb/repay conserves combined parent+child claim, credit and ordinary restore conserve claim on backed wf meters, and forfeit reduces it. Ordinary restore clears spill only; restore_to_entry clears spill and committed. Fresh root claim equals grant, giving an internal ceiling without external backing.
works_when: Primitive/adjacent meter interfaces proved in the probe; full list/opcode invariant still needs C1.3.4-.8.
evidence:
- episode:E0013
- episode:E0014
- source:prog/vfmCallMeterProbeScript.sml

## L0006 scope='C1.3' tags=run_call,termination,INL,Collect,trace
shape: Separate finite run existence from ordinary callee return
pattern: run_call_eq_tr is unconditional totality and run_call_finite_trace extracts a finite trajectory for either INL or abort. INL collection return separately needs reachable inner non-abort safety and handler wf/stack/gas conditions. Reuse totality and last-pop structural facts; propagate new scoped budget through run_call_reaches_inv rather than proving termination again.
works_when: Repairing collection-return machinery for fresh entered callees, with external caller unrestricted.
evidence:
- episode:E0014
- source:prog/AUDIT_seq58_call_safety.md
- tool_output:TO_seq58_progcall_port-20261031T123059Z_m0365_t001

## L0007 scope='C1.3' tags=budget,chain,TAKE,push,pop,grant
shape: Lift meter scalar contracts through a rooted selected context prefix
pattern: Use call_meter_chain above cs with accumulated descendant claim; its indexed equivalence gives the intended EL/TAKE budget. Top replacement needs backing and claim nonincrease; insertion/removal needs combined claim and local backing margins. Use call_meter_budget_push/pop and call_meter_entry_budget rather than redoing prefix arithmetic. At push compare with original pre-grant state, not already depleted parent. Root exit discharges without constraining external caller.
works_when: Infrastructure in vfmCallBudgetTheory and bounded entry shape contracts are available.
evidence:
- episode:E0015
- episode:E0018
- source:prog/vfmCallBudgetScript.sml
- source:prog/vfmCallEntryScript.sml

## L0008 scope='C1.3.6' tags=primitive,error,grant,claim,refund
shape: Primitive result-state meters versus refundable execution-grant transfer
pattern: call_meter_result fixes context tail, backing, gas bound and claim nonincrease for every result, including errors; call_meter_result_budget lifts it. Grants require call_meter_grant_result instead: own meter plus grant <= used and new claim + grant = old claim. Return-grant composition restores original claim using backed restore_child_gas boundary. These meter predicates do not themselves exclude Impossible; add separately checked safety adapters.
works_when: Composing CALL/CREATE or handler primitives using checked vfmCallMeterTheory boundaries.
evidence:
- episode:E0016
- source:prog/vfmCallMeterScript.sml
- episode:E0017

## L0009 scope='C1.3.6' tags=call_meter_safe,bind,error,neutral,result,precompile
shape: Compose all-result fixed-tail contracts through meter-changing frame-local computations.
pattern: call_meter_safe tracks postconditions on every result and excludes forbidden errors independently. Lift a contract quantified over ready current frames to precondition call_meter_result using call_meter_safe_result_lift and result transitivity. Keep result abstract; extract only the current context witness. Neutral updates preserve gasLimit/gasUsed/spilled/committed, allowing other fields to change. Use BETA_TAC after LET/function rewriting before HO matching.
works_when: Frame tail remains fixed and claims only decrease; grant transfer/push require separate stronger interfaces.
evidence:
- episode:E0019
- episode:E0020
- episode:E0021
- source:prog/vfmCallPrecompileScript.sml

## L0010 scope='C1.3.6.4' tags=precompile,crypto,dispatch,SIZES_ss,option
shape: Spend-only precompile and guarded finite dispatch preservation.
pattern: Factor read/consume and optional-output skeletons; split only opaque crypto return cases. Combine individual contracts after enumerating precompile_addresses, using SF wordsLib.SIZES_ss for word-literal comparisons. Retain membership to exclude dispatch's Impossible default. Lift final result to rooted budget with call_meter_result_budget.
works_when: unspecified
evidence:
- episode:E0021
- source:prog/vfmCallPrecompileScript.sml
- tool_output:TO_seq58_progcall_port-20261031T133309Z_m0655_t001

## L0011 scope='C1.3.6.5' tags=reservation,margin,stipend,charge,credit,claim
shape: Transport paid stipend/grant credit through frame-local operations before abort or child entry.
pattern: Use fixed-anchor reserved c k: current spill+committed+k <= used, gas bound, and claim(current)+k <= claim(c). Zero equals ordinary result; neutral updates and charge/credit preserve k. Ordinary result cannot recover k. Successful opcode cost payment acquires margin; zero-cost call_gas converts stipend margin into full grant reservation; restore/entry spends it.
works_when: Using checked EntryStep scalar boundaries and Reserve transport laws; ordinary early-error paths may forget reservations.
evidence:
- episode:E0023
- episode:E0024
- source:prog/vfmCallReserveScript.sml

## L0012 scope='C1.3.6.5.1' tags=reader,polymorphism,ISPEC_THEN,beta
shape: Instantiate a polymorphic context-reader boundary with numeric or address projections.
pattern: Explicitly quantify the reader f; specialize with Q.ISPEC_THEN on the small projection lambda, then MATCH_ACCEPT_TAC o BETA_RULE. Q.SPEC_THEN cannot instantiate the result type, and unnormalized beta redexes prevent direct matching.
works_when: Reader result type differs from the generic theorem's free type variable.
evidence:
- tool_output:TO_seq58_progcall_port-20261031T134530Z_m0751_t001
- source:prog/vfmCallReserveScript.sml

## L0013 scope='C1.3.6.5' tags=call_meter_safe,eta,bind,reservation,budget
shape: Safe bind continuation introduces eta-expanded reservation preconditions that resist direct boundary matching.
pattern: Apply antecedent-bearing boundary via drule_all, then rewrite/simp call_meter_safe_def and BETA_TAC to normalize pre/post predicates; use a small metis or disch_then drule_all to specialize the remaining universal contract. Reassert n<=LENGTH anchor.contexts after gvs if it normalized away. For neutral prefix-to-budget composition reuse call_meter_reserved_budget_bind, which forgets reservation only on early errors.
works_when: Checked safe contracts share the same fixed anchor and context tail; no implementation unfolding is needed.
evidence:
- episode:E0027
- episode:E0028
- source:prog/vfmCallStepsScript.sml
- tool_output:TO_seq58_progcall_port-20261031T142258Z_m0875_t001

## L0014 scope='C1.3.6.5' tags=UNCURRY,pair_CASE,BETA_TAC,eta,record-selector
shape: Whole opcode LET/paired-lambda suffix fails to match checked case-based reservation contract.
pattern: Normalize paired lambda with rewrite_tac[pairTheory.UNCURRY_pair_CASE,combinTheory.C_DEF] then BETA_TAC. For eta-shortened predicates normalize both goal and theorem, e.g. simp[SF ETA_ss] then irule (SRULE [SF ETA_ss] boundary). If .code still mismatches inspect inferred record type: annotate account_state explicitly rather than searching harder.
works_when: Composing state-gas entry suffix contracts with step_call/step_create monadic spines; matching issue is representational, not missing arithmetic.
evidence:
- episode:E0030
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m0969_t001
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m0973_t001
- source:prog/vfmCallStepsScript.sml

## L0015 scope='C1.3.7' tags=saved_context,reader,neutral,assert,call_meter_safe
shape: Opcode reads a context, asserts guards, then writes a record update of the saved context.
pattern: Use call_meter_safe_saved_context to retain the exact live head through a continuation with precondition call_meter_ready d; use ready_assert_prefix and set_neutral to finish. Invariant-only current_inv cannot justify writing back the saved value. For ready-to-ready primitive boundaries, convert post to result explicitly with call_meter_ready_result before result_lift.
works_when: No meter-changing operation intervenes between saved read and neutral replacement; neutral preserves gasLimit, gasUsed, spilled and committed.
evidence:
- episode:E0034
- source:prog/vfmCallInnerScript.sml
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1106_t001

## L0016 scope='C1.3.7' tags=simp,call_meter_safe,conditional,interface
shape: Conditional primitive contains return in one branch and an existing safety contract in the other.
pattern: Split the condition; simplify return branch with call_meter_safe_def/return_def and the nontrivial branch solely with its boundary theorem. Including safe_def in a combined simp list can unfold the contract before the boundary rewrite fires.
works_when: unspecified
evidence:
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1157_t001
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1159_t001

## L0017 scope='C1.3.7.5' tags=dispatch,is_call,PC,budget
shape: Combine fixed-tail ordinary instructions and stack-changing CALL/CREATE into step_inner.
pattern: First prove ordinary instruction and instruction-plus-PC fixed-tail contracts. Lift ordinary sequences to budget using original head backing/wf; CALL/CREATE use entry budget contracts and inc_pc_or_jump is return (). For finite dispatch use gvs[is_call_def] to eliminate contradictory constructor assumptions before applying entry contracts.
works_when: unspecified
evidence:
- episode:E0039
- source:prog/vfmCallInnerScript.sml:927-1041

## L0018 scope='C1.3.8' tags=settlement,record-update,claim,absorb,pop
shape: Semantic pop produces a repeated merged context expression that is expensive to normalize.
pattern: Define settlement over an arbitrary merged context, prove backing and claim conservation before substitution, then derive absorption/pop corollaries. Rewrite exact pop with call_meter_pop_settle_pair and consume call_meter_settle_pop_backed/claim without unfolding meter definitions.
works_when: Success repayment and failure creation-credit both subtract bounded spill from gasUsed and spilled; parent margin and parent gas upper bound supply the scalar conditions.
evidence:
- episode:E0042
- episode:E0043
- source:prog/vfmCallMeterProbeScript.sml:380-501

## L0019 scope='C1.3.8.2' tags=root-exit,observation,budget,output,ho_match_mp_tac
shape: Post-pop observation updates must preserve a budget even when the exposed caller is not backed.
pattern: Separate observation-only meter equality from backed fixed-tail contracts. call_meter_budget_observation splits active-prefix replacement from exited length; output safe contracts preserve budget/nonempty and compose with ho_match_mp_tac call_meter_safe_ignore_invariant for expanded predicate lambdas.
works_when: inc_pc, return data, memory and stack updates preserve gas scalar fields and context count; push failure is an ordinary StackOverflow and preserves state.
evidence:
- episode:E0045
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1340_t001

## L0020 scope='C1.3.8' tags=wf_context,decreases_gas_cred,handler,step_inner
shape: Handler budget proof needs intermediate gas upper bounds but no full account/state invariant
pattern: Strengthen the handler boundary input to EVERY (wf_context o FST) contexts. Extract this intermediate invariant from decreases_gas_cred_step_inner by unfolding decreases_gas_cred_def only in a boundary lemma; use its empty-context clause separately. This avoids synthesizing wf_state on failed inner states.
works_when: Handler consumes only top and parent context wellformedness; accounts and other state invariants are irrelevant to its budget argument.
evidence:
- episode:E0048
- source:prog/vfmCallInnerScript.sml:1468-1502

## L0021 scope='C1.3.9' tags=Collect,OWHILE,budget,gas_stack_ok,finite_return
shape: Scoped nonabort inner execution must yield finite ordinary collection-mode run return
pattern: Propagate ISL,wf_state,rooted budget and Collect through OWHILE_INV_IND. Inner budget theorem excludes Impossible/Unimplemented; collection mode excludes OutsideDomain. Existing step_inner stack_room/gas_stack preservation and handle_step_not_abort_returns_inl discharge handler INL, including final root pop. Then combine unconditional run_call_eq_tr and run_call_inl_length.
works_when: Initial state is wf, has rooted budget at its entry depth, and has at least two contexts.
evidence:
- episode:E0049
- source:prog/vfmCallReturnScript.sml

## L0022 scope='C1.3.8' tags=polymorphic,Cases_on,handle_create,unit
shape: Case equation for handle_create fails to rewrite the live handler case despite identical printed terms
pattern: handle_create's result is polymorphic. Annotate Cases_on `(handle_create e s) : unit execution_result` when composing handle_step; otherwise the case equation can belong to a distinct type instance and will not rewrite the live unit result.
works_when: Composing a polymorphic reraising operation with a unit-typed handler.
evidence:
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1418_t001
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1420_t001
- source:prog/vfmCallInnerScript.sml:1450

## L0023 scope='C1.3.10' tags=return,refund,Reverted,restore,settle,projections
shape: Final CALL memory return with arbitrary suspended external caller
pattern: Bound both actual call_return_gas and gasLimit-(gasUsed-(if e=NONE then 0 else spill)) by root claim/ceiling. This supplies the exact handler boundary without external caller backing. Represent returned caller with call_return_context using call_meter_settle; consume observation/meter projections rather than expanding absorb/repay records.
works_when: Fresh-root budget is initialized and ceiling<=caller.gasUsed; finite root return isolated via last_pop.
evidence:
- episode:E0050
- source:prog/vfmCallReturnScript.sml
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1544_t001

## L0024 scope='C1.3.11' tags=stipend,consume_gas,cutoff,call_gas,type
shape: Stipend CALL preservation after upfront execution cost
pattern: Successful consume affordability plus prefix-head gasLimit<=stipend and call_value_cost>stipend forces value=0. Make cutoff value explicitly num; creation charge/credit then simplify to false, and a separate get_gas_left/call_gas(0,...,0,0) continuation bounds child grant. Continuation must retain both dg and cg arguments because consume_gas dg remains in suffix.
works_when: unspecified
evidence:
- source:prog/vfmProgCallScript.sml:502-585
- episode:E0053

## L0025 scope='C1.3.11' tags=handler,INL,observation,rollback,trace
shape: Meter-independent stipend footprint through frame handlers
pattern: Prove metadata/context/rollback observations only for actual successful handle_exception result, eliminating intermediate failures by INL. Restrict local step stipend preservation to INL; run_call_reaches_inv already quantifies successful steps. This avoids needing restored-refund bounds in observation consumers.
works_when: unspecified
evidence:
- source:prog/vfmProgCallScript.sml:587-770
- episode:E0053

## L0026 scope='C1.3.11' tags=last_pop,success,b2w,return_context
shape: Align return and footprint witnesses with independent final errors
pattern: Apply call_memory_final_pop to footprint theorem's final event using the same rooted budget. Compare its t.contexts with run_call_memory_returns' t.contexts; call_return_context_observations projects stack b2w(error=NONE)::caller.stack. Case-split both NONE tests to establish equivalent success, not equality of arbitrary error witnesses.
works_when: unspecified
evidence:
- source:prog/vfmProgCallScript.sml:948-962
- episode:E0054

## L0027 scope='C1.4' tags=COND_RATOR,gvs,conditional,alias
shape: Conditional monadic function applied to state equals conditional execution results
pattern: Normalize with COND_RATOR before expanding branches. After gvs eliminates scalar aliases, split only the actual goal guard (e.g. IF_CASES_TAC), not a stale named expression. This avoids duplicate continuations and unrelated branch assumptions.
works_when: unspecified
evidence:
- episode:E0055
- episode:E0056
- source:prog/vfmProgCallScript.sml:1112
