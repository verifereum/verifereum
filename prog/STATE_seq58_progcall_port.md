# STATE_seq58_progcall_port
Updated: 2026-10-31

## Cursor
- component: C1.4
- status: in_progress
- active_file: prog/vfmProgCallScript.sml
- next_action: Restate call_entry_prepared (~967-1029) to the state-gas charged spine and exact conditional context output matching checked call_returns_summary (~852-965). Read sibling step_call_prepared (prog/vfmProgScript.sml:5843-5910) and port charge triplet, reservoir cover, literal upfront execution arithmetic, caller.stateGasLeft subtraction and authorized post-credit bound. No C1.4 edits yet. C1.3.11 proved/reviewed and committed 7c0ad8a1; all C1.3 leaves complete.
- expected_goal_shape: Latest build checks Finalise call_returns_summary then fails in old call_entry_prepared[normalize_entry] at QED (~1093): nested consume_gas/charge_new_account cases, obsolete new_account_cost and pre-upfront call_gas assumptions. Statement must be ported before tactical repair. C1.4 compose_entry also still expects old gasUsed-only summary.
- verify_with: holbuild(targets=["vfmProgCallTheory"], timeout=1800)

## If This Fails
- Inspect charged entry boundary without unfolding entire continuation. Record useful partial evidence with checkpoint_progress; request strategist interface repair if exact conditional prepared-entry formulation is unclear. Do not edit exported rules until C1.4 is checked.

## Do Not Retry
- Recover old call_gas-before-consume spine or new_account_cost execution summand: Semantics consumes base execution gas before charge_new_account and computes call_gas with mc=oc=0.
  - evidence: tool_output:TO_seq58_progcall_port-20261031T152132Z_m1584_t001
  - evidence: tool_output:TO_seq58_progcall_port-20261031T211644Z_m1656_t001
- Restore unrestricted safety or infer restored refund bound from old gas_stack_ok: Refund restoration increases refundable gas; checked rooted safety and successful-result observation already replace this invalid chain.
  - evidence: episode:E0053
  - evidence: episode:E0054
- Initialize fresh root with call_meter_entry_budget or restore caller.gasUsed-gasLeft summary equality: Root prefix excludes external caller, and parent spill repayment contributes additional execution gas. Use singleton root budget and exact call_return_context_meter.
  - evidence: tool_output:TO_seq58_progcall_port-20261031T152132Z_m1620_t001
  - evidence: episode:E0054

## Reflection
### Tunnel Vision Check
- Fresh expert should question reuse of sibling prefix machinery: step_call_prepared is exported but only handles success; call_prefix_prog_apply_result and step_call_prefix_bridge are local in sibling (~5178,5292), so not directly reusable. Existing finite spine peel may be simpler than exporting/rebuilding those interfaces.
- Do not optimize the old normalization before restating its obsolete cost and meter contract. Match prepared-entry output to the exact call_returns_summary rather than reconstructing huge semantic record expressions.
- The PLAN abstraction is now appropriate: completed safety/return layers supply context-valued boundaries; C1.4 is charge normalization and composition only.

### What Went Wrong
- Old stipend charge helper encoded call_gas before combined consume; actual semantics charges base execution first. Replaced with upfront affordability cutoff and zero-value call_gas continuation.
- Generic cutoff value required explicit :num annotation because after removing call_gas its type defaulted incorrectly.
- Initial independent last-pop errors were not automatically equal. Used call_memory_final_pop on the stipend footprint event and final context stack equality to equate success booleans; Cases_on both err=NONE guards closes b2w injectivity.
- Grouping C1.3 retained stale Risk 3 after all descendants finished, blocking C1.4. Strategist lowered group risk to 2; no extra probes needed.

### Ignored Signals
- Arbitrary handler result rollback was not safe after partial pop/refund failure. Successful handler observation and successful trace step restriction were sufficient for all stipend consumers.
- Full target not clean despite complete summary prefix: downstream entry normalization is genuinely stale and must not be advertised as passed.

### Strategy Adjustments
- Checked call_abort_context_pair, stipend CALL/step/reachability chain, successful handler observation, run_call_stipend_footprint and exact call_returns_summary. Removed duplicate obsolete unrestricted chain via vfmCallReturn interfaces.
- Fresh singleton child budget is initialized by definition, not call_meter_entry_budget, avoiding external caller backing.
- C1.3.11 summary now exposes credited-abort or call_return_context on reservoir-drained parent; gasLeft is child return gas only, not total caller refund.
- Bounded checked-prefix commit explicitly authorized by strategist despite unchanged downstream proof failure. Commit 7c0ad8a1 includes only task-owned prog changes and required trailers.

### Oracle Feedback
- E0054 review accepted bounded C1.3.11 proof; main build advanced to C1.4 normalize_entry.
- Strategist authorized exact conditional summary and local call_abort_context; no additional export hypotheses.
- Scheduling reconciliation accepted all C1.3 leaves done and authorized C1.4. No source actions or builds performed for C1.4 yet.

## Evidence Pointers
- episode:E0054 - checked and reviewed stipend/exact summary integration
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1644_t001 - build passes Finalise call_returns_summary, fails downstream old normalize_entry
- tool_output:TO_seq58_progcall_port-20261031T211644Z_m1647_t001 - E0054 accepted
- tool_output:TO_seq58_progcall_port-20261031T211644Z_m1649_t001 - grouping risk lowered and bounded prefix commit authorized
- tool_output:TO_seq58_progcall_port-20261031T211644Z_m1653_t001 - checkpoint commit 7c0ad8a1
- tool_output:TO_seq58_progcall_port-20261031T211644Z_m1656_t001 - sibling charged prepared-entry statement and proof
- tool_output:TO_seq58_progcall_port-20261031T211644Z_m1657_t001 - current obsolete prepared-entry source
- tool_output:TO_seq58_progcall_port-20261031T211644Z_m1659_t001 - C1.4 active scheduled frontier
