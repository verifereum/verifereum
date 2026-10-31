# STATE_seq58_progcall_port
Updated: 2026-10-31

## Cursor
- component: C1.3.11
- status: in_progress
- active_file: prog/vfmProgCallScript.sml
- next_action: Build vfmProgCallTheory to validate the last unverified edit at call_stipend_prefix_proceed_zero (~461-487): direct stipend-prefix list calculation for child over reservoir-drained parent. Continue porting stipend and summary consumers in source order. C1.3.10 is proved/reviewed/committed (207422fb); current C1.3.11 cleanup edits are partial and uncommitted.
- expected_goal_shape: Last verified failure: call_stipend_prefix n A D oa (s with contexts := (child,s.rollback)::(FST(HD s.contexts) with stateGasLeft:=0,SND(HD s.contexts))::TL s.contexts). Latest proof splits s.contexts and unfolds only stipend-prefix list predicates; check generated tail name t'. Later consumers still assume old step_call spine and gasUsed-only summary.
- verify_with: holbuild(targets=["vfmProgCallTheory"], timeout=1800)

## If This Fails
- Inspect the current small stipend list goal and repair via existing head_update/push boundaries if direct normalization is brittle. Continue only C1.3.11. Record partial evidence with checkpoint_progress; if the handler/stipend interface needs structural redesign, close stuck and request strategist review. Never add exported caller backing.

## Do Not Retry
- Restore or repair unrestricted nonempty-context call_exn_safe_step_call/step_create chain: Invalid safety contract under state-gas refunds; rooted safety already replaces it in checked vfmCallInner/Return theories.
  - evidence: episode:E0050
  - evidence: episode:E0051
- Use old call_stipend_prefix_push directly on proceed_call's final pushed state: The parent is now drained before child push; establish stipend prefix on drained parent or prove the list predicate directly.
  - evidence: tool_output:TO_seq58_progcall_port-20261031T152132Z_m1570_t001
- Unfold merged semantic meter records in summary consumers: Use call_return_context_observations and call_return_context_meter, preserving restore/credit/repay distinctions at boundary level.
  - evidence: episode:E0050

## Reflection
### Tunnel Vision Check
- A fresh expert should first distinguish meter-neutral stipend observations from safety: footprint preservation on an actual returned handler result may not need the rooted budget at every helper, whereas nonabort and post-restoration refund do.
- Outside-the-box option: use generic actual-result handler structural laws from spec property theories for rollback/footprint instead of forcing the exact success-equation boundary's stronger refund premise into every stipend helper.
- Do not optimize the deleted unrestricted safety chain. The isolated return theory already supplies valid finite-return and exact context settlement.
- PLAN remains appropriate, but C1.3.11 spans substantial integration. Extract an internal observation boundary if the same drain/restore/credit frame reasoning repeats.

### What Went Wrong
- Porting old proceed_call proof without unfolding get_accounts and drain_state_gas_reservoir left nested monadic cases. Adding these exposed the true parent: reservoir drained to zero; old push lemma no longer matched.
- In call_memory_final_pop, irule/simp normalized LENGTH es.contexts in the goal but not the existing budget assumption. Direct metis_tac using call_return_reaches_budget and LESS_EQ_REFL avoided brittle normalization plumbing.
- General reachability-budget helper must require 2<=n and n<=initial context depth, matching checked step_budget; these are discharged at root entry.
- decide_tac did not compose a conditional post-restoration gas expression inequality; metis_tac[LESS_EQ_TRANS] immediately did.

### Ignored Signals
- The old handle_exception_memory_return premises used pre-restoration gas; old stipend handler proofs still use those inequalities and will need actual-result structural boundaries or scoped budget-derived restored bounds.
- Deleting obsolete helpers is not full integration: current summary and prepared entry statements still contain gasUsed-only records and old new_account_cost; their scheduled components retain responsibility.

### Strategy Adjustments
- C1.3.10 added call_return_gas/data/context, exact handler equation, rooted refund bound, structural metadata/last-pop/trace, call_memory_final_pop, run_call_memory_returns, observation/meter projections. Clean build and review accepted, committed 207422fb.
- C1.3.11 imported vfmCallReturn and removed ~1500 lines of duplicated/obsolete machinery from vfmProgCallScript. Structural consumer names now point to call_return_* facts. The main build reaches stipend-prefix proceed_zero; latest direct list repair remains unverified.
- Only prog/ files changed. Do not commit current partial main-theory integration until build-clean stable checkpoint is available.

### Oracle Feedback
- E0050 review accepted the isolated return interface, explicitly including REVERT restored-spill refund bound and no external caller backing.
- Acceptance does not certify exports. C1.3.11 must discharge root budget at fresh entry, layer stipend observations, remove obsolete consumers, and assemble the actual exact-meter summary.

## Evidence Pointers
- episode:E0050 - proved and reviewed exact final-pop and finite memory-return interfaces
- episode:E0051 - nonterminal C1.3.11 cleanup and stipend repair evidence
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1544_t001 - clean vfmCallReturnTheory with scalar and observation projections
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1546_t001 - strategist accepted bounded C1.3.10 scope
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1550_t001 - commit 207422fb
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1570_t001 - latest verified main-theory goal: child over drained parent
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1571_t001 - latest unverified stipend-prefix list repair
