# STATE_seq58_progcall_port
Updated: 2026-10-30

## Cursor
- component: C1.2.2
- status: in_progress
- active_file: prog/vfmCallRefundProbeScript.sml
- next_action: Build standalone probe baseline, then construct/check the complete state-gas-ported separation precondition and CALL code ownership for (INL (),refund_candidate_state) using evm2set_on and STAR_evm2set_with_original. All concrete cond clauses and no-normal-PC1 iteration are already checked. Bridge the guarded FUNPOW sequence to rel_sequence EVM_NEXT_REL and the frozen postcondition via EVM_SPEC_SEMANTICS/V_SPEC_CODE; do not report exported falsehood before this bridge is checked.
- expected_goal_shape: Precondition evaluates on an explicit evm domain with Stack,PC0,GasUsed0, four state-gas fields, MsgParams,Memory,Rollback,Msdomain,ReturnData,Exception(INL()),refunds,logs,OriginalAccounts and CALL code. Postcondition entails ISL exception and PC1, contradicted by refund_candidate_no_normal_successor_pc for every n.
- verify_with: holbuild(targets=["vfmCallRefundProbeTheory"], timeout=1800)

## If This Fails
- Record partial evidence with checkpoint_progress; if separation/SPEC interface is structurally hard, close stuck and request shallow oracle guidance. Preserve distinction between checked concrete execution and unchecked exported SPEC falsehood.

## Do Not Retry
- EVAL the original choice-based parse_opcode or full step_call: Timeouts; rewrite parse_opcode_cond_thm and load wordsLib for small parser computations; bounded monadic simplification for CALL.
  - evidence: episode:E0006
  - evidence: tool_output:TO_seq58_progcall_port-20261030T170049Z_m0124_t001
- Use256w witness to refute frozen exports: Checked fIN256w precompile_addresses contradicts explicit nonprecompile premise. Use separate100w candidate.
  - evidence: episode:E0007
  - evidence: source:prog/vfmCallRefundProbeScript.sml
- Maintain stipend<=gasUsed through creation refund from nonempty contexts alone: Checked local safety falsehood; do not silently add spill invariants or change semantics.
  - evidence: episode:E0004

## Reflection
### Tunnel Vision Check
- Fresh expert should question full separation ownership and code framing first: numerical conditions and execution obstruction are checked, but SPEC applicability is not.
- The prior256w witness was invalid because256 is now a precompile. New100w witness has checked nonmembership; do not conflate them.
- An alternative to writing a huge specialized SPEC negation is deriving a necessary normal-PC/exception reachability consequence of the frozen postcondition, then using the already checked no_normal_successor_pc lemma.
- Current shallow probe is appropriate; do not resume sibling proofs or optimize the old safety invariant until applicability is resolved.

### What Went Wrong
- Ground parse/word computation failed because standalone theory omitted Libs wordsLib; adding it resolved conditional opcode evaluation.
- Initial witness address256 silently violated an explicit exported premise. Checked membership exposed this; no exported falsehood was claimed.
- Review updated PLAN but left episode pending twice; explicit second review settled E0007. Five oracle calls used this session; avoid unnecessary redesign.

### Ignored Signals
- Precompile exclusion should have been checked before tracing the old witness. Historical address assumptions are unsafe on current semantics.
- Repeated unchanged word-comparison goals were a missing computation-library signal, not a parser decomposition problem.

### Strategy Adjustments
- Separate100w candidate now has wf, Impossible step, all concrete state-gas-ported cond clauses, guarded FUNPOW exception, and zero/positive-step normal-PC obstruction checked.
- Use observation facts for get_current_context and parsed lookup to unfold step without expanding large concrete states in consumers.
- Checked probes committed as45ce560d and fee3f429. Old partial vfmProgCallScript edits remain uncommitted and untouched; do not certify them as completed port.

### Oracle Feedback
- Strategist accepted E0007 only as partial evidence with an invalid exported witness, then authorized separate100w candidate at the same shallow component.
- Full separation precondition and actual SPEC obstruction are mandatory before claiming frozen export falsehood. E0008 is a nonterminal checkpoint, not component completion.

## Evidence Pointers
- episode:E0008 - current checked100w evidence and remaining bridge
- tool_output:TO_seq58_progcall_port-20261030T170049Z_m0203_t001 - final clean standalone probe build
- tool_output:TO_seq58_progcall_port-20261030T170049Z_m0187_t001 - E0007 reviewed;256w inadmissibility accepted
- source:prog/vfmCallRefundProbeScript.sml - candidate facts through no_normal_successor_pc
- source:prog/vfmProgScript.sml - EVM_SPEC_SEMANTICS around349, STAR_evm2set_with_original around368, EVM_NEXT_REL around322
