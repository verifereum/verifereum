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
