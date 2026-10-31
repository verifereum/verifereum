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
