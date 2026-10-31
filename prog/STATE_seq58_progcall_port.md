# STATE_seq58_progcall_port
Updated: 2026-10-31

## Cursor
- component: C1.3.6.5.3
- status: in_progress
- active_file: prog/vfmCallStepsScript.sml
- next_action: Build vfmCallStepsTheory to confirm current clean suffixes, then layer charge_new_account, conditional assert_not_static and expand_memory over call_meter_reserved_gas_tail using call_meter_reserved_budget_bind. Next acquire stipend reservation from opcode consume cost and compose initial pop_stack/readers. Grant component was proved/reviewed and committed 41906ccf; CallSteps checked partial work committed 33d9f96a and 085fbfef.
- expected_goal_shape: No current failing proof. gas_tail covers get_gas_left, call_gas pair, payment, balance/depth aborts and proceed_call. New prefix contracts should preserve reserved c margin on every result, lifting early errors to anchor budget. Whole step_call remains unwritten.
- verify_with: holbuild(targets=["vfmCallStepsTheory"], timeout=1800)

## If This Fails
- Inspect actual safe-contract and beta/eta matching before unfolding primitives. checkpoint_progress for useful partial proof; close stuck and request review only for structural interface/decomposition failure. Do not add export hypotheses.

## Do Not Retry
- Recover paid stipend/grant reservation from call_meter_result.: It forgets surplus; retain call_meter_reserved until refund or entry spends it.
  - evidence: episode:E0023
  - evidence: episode:E0024
- Unrestricted nonempty-context CALL safety or additional exported caller backing guards.: Historical counterexamples require scoped fresh-callee budget. No further export weakening is authorized.
  - evidence: episode:E0013
  - evidence: tool_output:TO_seq58_progcall_port-20261030T183500Z_m0272_t001
- Repeated direct irule/ho_match_mp_tac variants on safe precondition eta mismatch.: Use directed boundary premises and normalize call_meter_safe_def instead; tested on proceed/payment tails.
  - evidence: episode:E0027
  - evidence: source:prog/vfmCallStepsScript.sml

## Reflection
### Tunnel Vision Check
- The reservation decomposition remains valid: grant acquisition/discharge and all semantic suffixes now build without reopening precompile internals. We are not optimizing the wrong meter invariant.
- Outside-the-box option not tried: a compact semantic suffix definition to avoid repeatedly quoting the long monadic continuation. Current named suffix lemmas suffice, but ask strategist for source refactor if statement duplication obstructs prefix assembly.
- A fresh expert should first check that initial reader adapters retain return values and that zero-reservation early errors lift to the original anchor budget; do not demand success-only meter facts on errors.
- Too many direct matching retries were spent on eta-expanded preconditions. Use the checked directed safe_def boundary application pattern early rather than repeatedly trying irule/ho_match_mp_tac.

### What Went Wrong
- Partial predicate versus eta-expanded lambda caused direct irule and ho_match_mp_tac failures even when the mathematical contract matched. Directed drule_all followed by simp[call_meter_safe_def] and small metis proved the corresponding instantiated boundary.
- irule reordered conjunctions and inferred many existential parameters; guessed qexistsl argument orders failed. Read the live goal and supply only the remaining existential u.
- gvs again normalized n<=LENGTH u.contexts to n<=SUC(LENGTH rest), preventing drule_all. Reassert the literal boundary premise before application.
- Used wrong reader name once: correct lemma is call_meter_reserved_gas_left_reader.

### Ignored Signals
- Beta reduction and ready-to-result consequence are separate obligations. BETA_TAC is required after specializing bind continuation lambdas; ready-post does not syntactically match result-post.
- The persistent safe-contract mismatch was syntactic, not missing arithmetic or a false grant contract. Unfold only call_meter_safe_def at that boundary, not neutral monadic operations.

### Strategy Adjustments
- Continue suffix-to-prefix assembly. call_meter_reserved_budget_bind now packages reserved-neutral computation followed by a budget-post continuation, including error-state reservation forgetting.
- All new CallSteps proofs remain small and primitive bodies opaque. Keep this level; a growing monolithic step_call proof should trigger refactoring/escalation.
- Stable source checkpoints are committed. Latest CallSteps build is clean; whole-entry progress remains partial, not a claimed completion.

### Oracle Feedback
- E0026 accepted: grant boundary source covers consume acquisition, withholding, CALL payment, entry wrappers and all abort discharge adapters. No statement repair or PLAN changes were needed.

## Evidence Pointers
- episode:E0026 - grant component proved and reviewed
- tool_output:TO_seq58_progcall_port-20261031T140620Z_m0816_t001 - strategist acceptance
- episode:E0027 - checked CallSteps suffix/composition progress
- episode:E0028 - gas reader tail checked
- tool_output:TO_seq58_progcall_port-20261031T142258Z_m0875_t001 - latest clean vfmCallStepsTheory build
- tool_output:TO_seq58_progcall_port-20261031T142258Z_m0879_t001 - latest stable source commit 085fbfef
- source:prog/vfmCallStepsScript.sml
