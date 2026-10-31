# STATE_seq58_progcall_port
Updated: 2026-10-31

## Cursor
- component: C1.3.7.2
- status: in_progress
- active_file: prog/vfmCallInnerScript.sml
- next_action: Fix call_meter_safe_access_inv near line 375: after result_lift/gen_tac, forward-introduce GEN_ALL call_meter_safe_access_address, unfold call_meter_safe_def and discharge with call_meter_ready_result (as in memory_info_inv). Build; subsequent source readers and copy_source/copy_memory helpers are unverified. Then finish family opcode consumers.
- expected_goal_shape: forall d. call_meter_safe (call_meter_ready d rb rest) (access_address a) (lambda r t. call_meter_result d rb rest t). Existing access boundary returns ready, not result.
- verify_with: holbuild(targets=["vfmCallInnerTheory"], timeout=1800)

## If This Fails
- Inspect actual postcondition and use consequence or forward chaining to convert ready to result; checkpoint partial progress. Escalate only on structural interface failure, not routine beta/LET or postcondition matching.

## Do Not Retry
- Treat arbitrary set_current_context as preserving fixed-anchor result.: Saved context must be proven to be current; use saved_context boundary and neutral replacement.
  - evidence: episode:E0034
  - evidence: source:prog/vfmCallInnerScript.sml
- Infer paid grant reservation from ordinary call_meter_result or add external caller backing guards.: Result forgets surplus; rooted fresh-callee accounting and checked reservation are required. No further export weakening authorized.
  - evidence: episode:E0023
  - evidence: episode:E0024

## Reflection
### Tunnel Vision Check
- The fixed-tail ordinary-result abstraction remains appropriate; CALL/CREATE retain separate rooted-budget contracts. Do not try to force stack-extending entry into fixed tails.
- Outside-the-box option: generic reader-to-result adapter could replace repeated mp_tac/ready_result conversions. No need to redesign semantics or meter definitions.
- Fresh expert should inspect exact postconditions before using simp: a ready-preserving operation does not syntactically match a result-returning boundary.
- Remaining copy helpers explicitly parameterize source safety; verify their types and source case normalization rather than expanding every account/memory primitive.

### What Went Wrong
- Current access_inv proof assumed call_meter_safe_access_address returns call_meter_result; it actually preserves call_meter_ready. Build stops before the new copy helpers.
- CREATE condition normalization initially used GSYM DISJ_ASSOC, but HOL's DISJ_ASSOC associates right-nested disjunction to the left. Correct direction fixed whole CREATE matching.
- Saved-context proof needed gvs after stripping hypotheses; simp before introducing equalities cannot reduce conditional context readers/writers.

### Ignored Signals
- Exact ready-versus-result postconditions were underweighted again when composing access_address. Inspect signatures rather than guessing from theorem names.
- New suffixes after a failed earlier theorem are not checked: do not describe source-reader or copy combinators as proved yet.

### Strategy Adjustments
- CREATE whole entry is proved, reviewed and committed as 4912672c.
- Neutral stack/control-flow plus existing arithmetic/memory helper coverage is proved, reviewed and committed as 07009dd6.
- Continue only C1.3.7.2; C1.3.7.3 is a queued independent storage family, not current work.
- Use saved_context plus ready_assert_prefix/set_neutral for genuine saved-context updates; invariant-only current_inv suffices only when returned contexts are read but not written back.

### Oracle Feedback
- E0032 and E0034 accepted without contract changes. Reservation and saved-context boundary designs validated.
- Strategist refined broad C1.3.7 into five bounded family/dispatch children. Final dispatch waits for memory/read/log, storage, and terminal families.

## Evidence Pointers
- episode:E0032 - whole CREATE proof
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1042_t001 - CREATE stable commit
- episode:E0034 - neutral/control-flow family proved
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1096_t001 - stable Inner checkpoint commit
- episode:E0035 - current partial copy-family attempt
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1103_t001 - current access adapter failure
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1106_t001 - exact ready-preserving access signature
