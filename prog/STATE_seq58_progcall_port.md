# STATE_seq58_progcall_port
Updated: 2026-10-31

## Cursor
- component: C1.3.4
- status: ready
- active_file: prog/vfmCallMeterProbeScript.sml
- next_action: Begin C1.3.4, build vfmCallMeterProbeTheory baseline, then define rooted prefix/budget per PLAN and audit. Prove fresh-root initialization, active-top backing, root claim ceiling and exit discharge before list update/push/pop lifting interfaces. A separate prog theory importing the checked probe is permitted if better isolated.
- expected_goal_shape: prefix n s = TAKE (LENGTH s.contexts - n + 1) (MAP FST s.contexts); active budget bounds total claim by root grant and each selected frame's own spill+committed plus claims above by gasUsed. External caller excluded. Fresh root claim=tx.gasLimit and own backing=0; update/push/pop reduce to scalar inequalities already checked.
- verify_with: holbuild(targets=["vfmCallMeterProbeTheory"], timeout=1800); if introducing separate budget theory, build its logical Theory target too

## If This Fails
- Use checkpoint_progress for useful partial list-interface evidence; after structural failure or three honest attempts close_component stuck with exact build evidence and request scoped redesign. Do not begin C1.4 or all-opcode preservation until their prerequisites pass.

## Do Not Retry
- Prove unrestricted nonempty-context CALL exception safety or infer backing from wf_state.: Historical witness refutes the helper; wf_context has only stack/gasLimit/parsed-code conditions.
  - evidence: episode:E0011
  - evidence: source:prog/AUDIT_seq58_call_safety.md
- Use independent backing for every frame as nested-pop invariant.: Actual checked pop returns unused gas and destroys parent backing; need own backing plus descendant claims.
  - evidence: episode:E0013
  - evidence: source:prog/vfmCallMeterProbeScript.sml
- Require external caller backing, or reopen already-amended original export falsehood because old owner message is absent after context clear.: External caller must remain arbitrary; persisted authority permits only reservoir cover, creditBack and grant-survival guards, reaffirmed by whole-plan review.
  - evidence: tool_output:TO_seq58_progcall_port-20261030T183500Z_m0272_t001
  - evidence: tool_output:TO_seq58_progcall_port-20261031T123059Z_m0391_t001

## Reflection
### Tunnel Vision Check
- Fresh expert should question whether the proposed budget/list interface is compositional before investing in opcode proofs; checked adjacent algebra is not whole-prefix preservation.
- Do not optimize the false unrestricted call_exn_safe_step_call. The next abstraction is list budget lifting, then semantic primitive contracts.
- Termination is already unconditional via run_call_eq_tr; rebuilding a measure induction would optimize the wrong problem. Missing property is INL/non-abort return on reachable callee-prefix states.
- Outside-the-box option authorized by PLAN: isolate durable budget infrastructure in its own prog theory rather than fighting the broken production prefix.

### What Went Wrong
- Per-frame backing alone failed actual pop: parent gasUsed=spill=10, child unused grant=10. E0013 checks the counterexample; a descendant claim budget is necessary.
- C1.3.3 was originally non-executable diagnostic, so scheduler incorrectly advanced to C1.4 after probes. Scoped plan repair made the audit executable and subsequently assigned real missing proof leaves.
- An oracle review again lacked historical owner amendment context and requested whole-plan review. Providing authoritative persisted ruling m0272 resolved this; current PLAN reaffirms narrowly authorized guards.
- Unconstrained numeric budget probe needed explicit :num annotation before decide_tac could apply. Ordinary restore refunds only spill; full entry restoration refunds spill+committed, so corrected a misleading probe comment.

### Ignored Signals
- Total run_call existence does not imply successful collection return. Existing collection proof consumes the false unrestricted inner safety chain.
- gas_stack_ok omits own spill/committed and descendant committed; wf_state does not supply the new budget.
- Review acceptance of bounded probes is not preservation credit. E0014 required explicit new executable leaves before C1.4.

### Strategy Adjustments
- Committed reviewed nested-boundary probes as 61351e7d and finite-run audit/claim probes as 35d28914. Probe target clean; no main export proof claimed.
- Next executable frontier is C1.3.4; C1.3.5-.11 now own primitive, entry, opcode, handler, collection-return, final-pop and stipend/summary integration.
- Read prog/AUDIT_seq58_call_safety.md for exact premise/provider map and proposed signatures, rather than rediscovering termination and safety dependencies.
- Keep all edits under prog/ and preserve arbitrary suspended external caller meter.

### Oracle Feedback
- E0013 accepted only adjacent-frame boundary tests, not an inductive invariant.
- E0014 accepted only bounded audit and checked claim probes; missing preservation/summary outputs assigned C1.3.4-.11.
- TO_seq58_progcall_port-20261031T123059Z_m0391_t001 reaffirmed persisted owner amendment; do not reopen original counterexample as current stop gate absent new withdrawal.

## Evidence Pointers
- episode:E0013 - actual pop counterexample, strengthened adjacent margin and fresh entry probes
- episode:E0014 - finite-run audit and claim currency probes
- tool_output:TO_seq58_progcall_port-20261031T123059Z_m0384_t001 - latest clean vfmCallMeterProbeTheory build
- tool_output:TO_seq58_progcall_port-20261031T123059Z_m0391_t001 - authoritative amended-contract reaffirmation and new preservation leaves
- tool_output:TO_seq58_progcall_port-20261031T123059Z_m0393_t001 - E0014 accepted as bounded evidence
- tool_output:TO_seq58_progcall_port-20261031T123059Z_m0399_t001 - next frontier C1.3.4
- source:prog/AUDIT_seq58_call_safety.md - exact consumer signatures, missing obligations and proposed budget
