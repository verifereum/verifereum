# STATE_seq58_progcall_port
Updated: 2026-10-31

## Cursor
- component: C1.3.6.5.4
- status: in_progress
- active_file: prog/vfmCallStepsScript.sml
- next_action: Finish call_meter_reserved_create_grant_tail collision consequence near line 399: after simp add rpt strip_tac and metis_tac[call_meter_reserved_forget], inspecting the second residual goal if present. Build. Then compose CREATE charge/domain and early-abort suffixes and zero-reservation reader/check prefix. CALL is proved/reviewed and committed as 37466077; current uncommitted CREATE suffix is failing.
- expected_goal_shape: Collision branch leaves !s. call_meter_reserved c x rb rest s ==> call_meter_result c rb rest s. holbuild reports two residual goals; inspect the other if explicit forgetting does not close both. Withholding success bind prefix already checks.
- verify_with: holbuild(targets=["vfmCallStepsTheory"], timeout=1800)

## If This Fails
- Inspect actual consequence residual and use checked reservation-forgetting/result-abort boundaries; no primitive unfolding needed. checkpoint_progress for useful partial evidence; close stuck/review only for structural interface failure.

## Do Not Retry
- Recover paid stipend/grant reservation from ordinary call_meter_result.: It forgets backing surplus; retain reservation until refund or entry spends it.
  - evidence: episode:E0023
  - evidence: episode:E0024
- Repeated generalized metis searches on overloaded .code record-selector mismatches.: The delegate helper needed account_state annotation; inspect direct matcher type diagnostics first.
  - evidence: tool_output:TO_seq58_progcall_port-20261031T152132Z_m0969_t001
  - evidence: source:prog/vfmCallStepsScript.sml
- Unrestricted nonempty-context CALL safety or more caller-facing backing guards.: Historical counterexamples require rooted fresh-callee budget; no further export weakening authorized.
  - evidence: episode:E0013
  - evidence: tool_output:TO_seq58_progcall_port-20261030T183500Z_m0272_t001

## Reflection
### Tunnel Vision Check
- The reservation decomposition is validated by whole CALL proof; CREATE uses the same abstraction without stipend, so do not redesign meters or optimize a different invariant.
- Outside-the-box option still untried: semantic suffix definitions could shrink duplicated long statements, but current named suffix contracts permit a 30-line whole CALL assembly and remain adequate.
- A fresh expert should check overloaded record selectors and beta/eta normalization before treating a failed matcher as a missing mathematical lemma.
- Current CREATE failure is only consequence transport, not evidence of falsehood or a failed architecture. Do not reopen precompile internals or add exported guards.

### What Went Wrong
- Delegate helper initially inferred account as message_parameters because .code is overloaded. This caused repeated matching failures and metis timeouts; explicit (account:account_state) fixed the real mismatch.
- Paired lambdas from step_call LET rewriting did not match case-based suffix contracts until rewriting UNCURRY_pair_CASE and C_DEF followed by BETA_TAC.
- gvs can normalize away n<=LENGTH u.contexts; reassert literal premise before drule_all budget lifting.
- simp does not necessarily use call_meter_reserved_forget as an implication-closing rule; the current CREATE consequence requires explicit reasoning.

### Ignored Signals
- Delayed inspecting the direct irule error exposed a concrete record-selector type mismatch only after several unnecessary generalized metis attempts.
- irule rearranges conjunctions: do not assume existential anchor is first; read live goal before qexists.
- Eta-normalizing only the goal can cause different-constructor matching. Normalize the boundary theorem as well.

### Strategy Adjustments
- Continue CREATE suffix-to-prefix, reusing call_meter_reserved_budget_bind for neutral prefixes and call_meter_safe_anchor_budget for abort branches.
- CALL whole-opcode proof is committed and builds; do not include unfinished CREATE suffix in a stable commit.
- Keep metis small; use first_x_assum drule_all on isolated universal safe contracts where exact types match.

### Oracle Feedback
- E0030 accepted with no PLAN changes: whole CALL safety wrapper uses existing wf_state/positive protected-depth premises, does not weaken exports, and leaves semantics behind checked interfaces. CREATE is authorized next.

## Evidence Pointers
- episode:E0030 - whole CALL proved and reviewed
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m0981_t001 - clean CALL build
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m0983_t001 - strategist acceptance
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m0987_t001 - stable commit 37466077
- episode:E0031 - partial CREATE suffix attempt
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m0993_t001 - current failure and residual collision consequence
- source:prog/vfmCallStepsScript.sml
