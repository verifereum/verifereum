# STATE_seq58_progcall_port
Updated: 2026-10-31

## Cursor
- component: C1.3.2
- status: in_progress
- active_file: prog/vfmCallMeterProbeScript.sml
- next_action: Begin/reaffirm C1.3.2 and build vfmCallMeterProbeTheory baseline. Then probe two-frame internal pop: construct checked counterexample to per-frame backing alone (parent gasUsed=spill=10, child unused grant=10, child spill=committed=0, no reservoir repayment). Test the planned strengthened parent margin including descendant refundable grant, using actual absorb/repay and failure restore/credit equations. No C1.3.2 source edits yet.
- expected_goal_shape: Individual call_meter_backed holds for fresh callee and primitive transitions, but parent spill+committed may cease to be backed after subtracting child gasLeft. Expected sufficient residual is parent own backing plus child's gasLeft+spill+committed <= parent.gasUsed; test success/failure separately and do not impose this on final external caller.
- verify_with: holbuild(targets=["vfmCallMeterProbeTheory"], timeout=1800)

## If This Fails
- For bounded probe counterexamples record checked evidence without claiming export falsehood. Use checkpoint_progress for partial results. If invariant interface fails structurally, close C1.3.2 stuck and request scoped redesign. Do not resume main-file opcode proofs before nested-boundary and finite-run strategy checkpoints.

## Do Not Retry
- Prove call_exn_safe_step_call from merely nonempty contexts or derive spill backing from wf_state.: Historical checked witness falsifies unrestricted safety; scoped backing is not part of wf_context.
  - evidence: episode:E0011
  - evidence: source:prog/vfmCallRefundProbeScript.sml
- Treat original unguarded export falsehood as a current stop gate after owner amendment.: Owner explicitly authorized only sibling coverage, creditBack and survival guards; strategist reconciled task and retained counterexample as historical evidence.
  - evidence: tool_output:TO_seq58_progcall_port-20261030T183500Z_m0272_t001
- Require backing on every context including suspended external caller.: Would leak an unauthorized hypothesis into exported rules; scoped callee invariant excludes external suffix.
  - evidence: tool_output:TO_seq58_progcall_port-20261030T183500Z_m0294_t001

## Reflection
### Tunnel Vision Check
- Fresh expert should challenge nested-pop preservation first: per-frame backing has only been established for individual meter operations, not gas transfer between frames.
- Alternative worth auditing in C1.3.3: reuse existing run_call finite trace/measure machinery rather than rebuilding opcode-wide exception safety. Check whether its hypotheses depend on the arbitrary suspended caller.
- Do not optimize the existing call_exn_safe_step_call proof: its nonempty-only statement is false. Primitive safety combinators remain useful, but compound execution needs a scoped invariant.
- Current shallow probes are appropriate. The planned descendant-budget strengthening is a candidate, not an established invariant; check committed balances and restoration as carefully as spill.

### What Went Wrong
- Original frozen rules admitted a checked counterexample. Owner explicitly amended the task to permit sibling-style coverage, creditBack and grant-survival guards; the old stop decision is superseded only to that narrow extent.
- Strategist initially misclassified the explicit owner task amendment as an impermissible directive. A follow-up resolved precedence and authorized continuation.
- Main-file unrestricted call_exn_safe_step_call remained false despite guarded exports. E0011 forced a scoped callee-prefix redesign instead of tactic patches.
- MIN arithmetic needed MIN_DEF splitting before decide_tac. Charge simplification needed branch splits and live context assumptions before monadic evaluation.

### Ignored Signals
- An authorized initial-CALL guard cannot justify safety of every arbitrary intermediate nonempty state.
- wf_state does not entail spill backing; the callee starts with zero spill, while the externally suspended caller must remain unconstrained.
- Episode review accepts evidence but often does not redesign the plan. A separate replacement call was needed after accepted E0011 left no frontier.

### Strategy Adjustments
- C1.8 guarded charge/credit/abort boundary equations committed as 3f361b34. They build through the boundary prefix; vfmProgCallTheory still fails later in old safety machinery.
- C1.3.1 completed and reviewed E0012. Standalone backing/margin probes committed as 4ce766e4; target vfmCallMeterProbeTheory clean.
- C1.3.2 has just begun; no source changes or new proof-search evidence for it. Do not create a handoff-only episode.
- Keep semantic changes out of spec/. Record owner's invariant rationale rather than proposing a semantics repair: backed reachable callee states exclude the historical witness, but no global spill<=g hypothesis is authorized on exports.

### Oracle Feedback
- Accepted E0010 only as guarded boundary-prefix evidence, not full theory completion.
- Accepted E0011 as wrong-statement blocker and replaced C1.3 with initialization, nested-prefix and finite-consumer probes.
- Accepted E0012: sp+committed<=gasUsed is initialized and preserved by the tested meter operations; actual consume/charge/credit stipend margin includes spilling. This does not certify nested frame or final-pop safety.

## Evidence Pointers
- episode:E0012 - checked primitive backing and stipend-margin probes
- tool_output:TO_seq58_progcall_port-20261031T122504Z_m0321_t001 - clean standalone meter-probe build
- tool_output:TO_seq58_progcall_port-20261031T122624Z_m0323_t001 - accepted E0012 review
- tool_output:TO_seq58_progcall_port-20261030T183500Z_m0294_t001 - scoped C1.3 probe redesign
- tool_output:TO_seq58_progcall_port-20261031T122624Z_m0328_t001 - repay_state_gas_spill_context exact meter equations
- source:prog/vfmCallMeterProbeScript.sml - durable meter probes committed4ce766e4
- source:prog/vfmProgCallScript.sml - guarded boundaries and still-unrepaired main safety chain
