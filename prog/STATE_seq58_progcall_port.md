# STATE_seq58_progcall_port
Updated: 2026-10-31

## Cursor
- component: C1.6
- status: in_progress
- active_file: prog/vfmProgCallScript.sml
- next_action: Restate SPEC_Call_any (~1284) and SPEC_Call_stipend (~1352) to the charged precondition and exact semantic meter post, then validate shared tactics. C1.6 begun but no source edits yet. Read checked call_entry_prepared (~967), call_final_context_observations (~1211), call_return_context_meter (prog/vfmCallReturnScript.sml:596), and sibling meter packaging (prog/vfmProgScript.sml:6776-6839). If exact export meter relation is ambiguous, request strategist statement guidance before inventing it. C1.4/C1.5 committed as 04f8b947/a15533d9.
- expected_goal_shape: Latest target build checks all helper/framing proofs and ML declarations, fails at call_spec_entry_tac in obsolete SPEC_Call_any: old new_account_cost and no meter resources cannot instantiate charged prepared-entry. Shared tactic applications still unvalidated.
- verify_with: holbuild(targets=["vfmProgCallTheory"], timeout=1800)

## If This Fails
- Inspect isolated tactic stage after export restatement; checkpoint_progress for useful partial evidence. Escalate contract/interface ambiguity or new obstruction rather than adding hypotheses. Close only terminal proof outcomes.

## Do Not Retry
- Use old new_account_cost execution summand or call_gas before upfront consume: Charged entry is now checked with upfront base execution consumption and call_gas mc=oc=0.
  - evidence: episode:E0056
- Identify caller final gasUsed with caller.gasUsed-gasLeft: gasLeft bounds child unused execution gas only; spill repayment and creation credit add recovery.
  - evidence: tool_output:TO_seq58_progcall_port-20261031T211644Z_m1730_t001
  - evidence: source:prog/vfmCallReturnScript.sml:596
- Validate prepared shared tactics using old no-meter SPEC statements: Those statements lack the new prepared-entry premises; expected failure is not evidence tactics are defective.
  - evidence: episode:E0058

## Reflection
### Tunnel Vision Check
- Fresh expert should first question exact exported meter post formulation: child gasLeft is not total caller refund; arbitrary existential final meters would weaken the contract.
- C1.5 validation was circular against obsolete exports. Strategist fixed abstraction: checked conditional observation theorem now; actual tactic applications in C1.6.
- Do not optimize old export tactics before restating their obsolete cost and ownership contracts. Exact conditional context boundary is available; no new execution invariant should be needed.
- Potential alternative not explored: express post settlement via sibling-style merged context/credit_new_account_context rather than exposing helper-defined call_abort_context/call_return_context in public statements. Strategist owns this choice if frozen-content interpretation is unclear.

### What Went Wrong
- C1.4 normalization expanded six large branches and split on a value alias eliminated by gvs. E0055 escalated; COND_RATOR plus splitting the actual remaining guard closed it.
- Global AC simplification timed out and was removed. A small adjacent-add identity proved by decide_tac handled final meter sum alignment.
- Initial compose_entry retained obsolete cg<=dg+mc and omitted err witness. Replaced with authorized caller post-credit bound and exact context summary.
- Shared entry now abbreviates final context and derives observations, but this code has only been ML-typechecked, not successfully applied. Do not report end-to-end tactic validation.

### Ignored Signals
- Conditional monadic-function application, not semantic execution complexity, caused the normalization residual. Should have used COND_RATOR earlier.
- Forward matching call_returns_summary required charged equality against rb'.accounts explicitly; scalar aliases alone were not syntactically sufficient.
- Successful prefix build is not a clean target: old exported statements still fail.

### Strategy Adjustments
- Keep all non-meter observations via checked call_final_context_observations; meter projections must follow exact semantic settlement.
- C1.4 and bounded C1.5 are reviewed and committed. No source edits for C1.6 yet; no further export guards authorized.
- Retain creation reservoir cover, creditBack=MIN stateCost sp and previously authorized calleeGas post-credit bound only; any conflict with task frozen content needs explicit review.

### Oracle Feedback
- E0056 accepted charged prepared-entry boundary; bounded commit allowed despite downstream framing failure.
- E0058 accepted checked framing/conditional observation helper plus prepared tactic declarations only; full shared-tactic validation explicitly deferred to C1.6.
- C1.5 repaired PLAN warns not to identify final.gasUsed with caller.gasUsed-gasLeft: entered spill settlement and no-entry creation credit are additional recovery.

## Evidence Pointers
- episode:E0056 - checked charged prepared-entry closure
- episode:E0058 - bounded framing/observation closure, applications deferred
- tool_output:TO_seq58_progcall_port-20261031T211644Z_m1738_t001 - latest build reaches old SPEC_Call_any
- tool_output:TO_seq58_progcall_port-20261031T211644Z_m1730_t001 - exact conditional observation interface and post packaging constraints
- tool_output:TO_seq58_progcall_port-20261031T211644Z_m1740_t001 - bounded C1.5 review acceptance
- tool_output:TO_seq58_progcall_port-20261031T211644Z_m1744_t001 - checkpoint commit a15533d9
- tool_output:TO_seq58_progcall_port-20261031T211644Z_m1746_t001 - sibling semantic merged-meter packaging
