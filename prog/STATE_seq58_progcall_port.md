# STATE_seq58_progcall_port
Updated: 2026-10-31

## Cursor
- component: C1.3.6.2
- status: in_progress
- active_file: prog/vfmCallMeterSafeScript.sml
- next_action: Build newly drafted vfmCallMeterSafeTheory first; it has NEVER been built. Fix contract-law proofs from reported goals, then add remaining consume-followed-by-return and backed return-grant probes required by C1.3.6.2. Current file drafts safe definition, return/fail/consequence/bind/ignore-bind/invariant/from-result laws, consume adapter and early-failure probe.
- expected_goal_shape: call_meter_safe P m Q tracks Q on all result states and excludes SOME Impossible/Unimplemented on INR. Bind splits g s into pair and sum, passes R only on success, and retains Q on error. Likely first errors are ordinary typing or bind/invariant tactic matching in this unverified draft.
- verify_with: holbuild(targets=["vfmCallMeterSafeTheory"], timeout=1800)

## If This Fails
- Inspect exact build goal and repair only active contract/probe scope. If definition interface proves structurally hostile or after three honest approaches, close_component stuck with evidence and request review. Do not unfold whole step_call or proceed precompile bodies; C1.3.6.3-.5 now explicitly own those prerequisites.

## Do Not Retry
- Unrestricted nonempty-context CALL safety or infer backing from wf_state: Historical counterexample refutes it; backing must come from fresh-root descendant budget.
  - evidence: episode:E0011
  - evidence: episode:E0013
- Constrain external caller or reopen original export falsehood solely because historical owner message is absent: Persisted amendment permits only reservoir cover, creditBack and grant-survival guard; external caller remains arbitrary.
  - evidence: tool_output:TO_seq58_progcall_port-20261030T183500Z_m0272_t001
  - evidence: tool_output:TO_seq58_progcall_port-20261031T123059Z_m0391_t001
- Unfold whole step_call/proceed_call/dispatch together or copy old safety-only library wholesale: Missing all-result monadic and precompile interfaces now have explicit PLAN leaves; large semantic goals are an abstraction failure.
  - evidence: episode:E0017
  - evidence: tool_output:TO_seq58_progcall_port-20261031T123059Z_m0515_t001

## Reflection
### Tunnel Vision Check
- Fresh expert should first test whether the result-indexed bind law composes naturally without copying full assumptions or rebuilding the old 1500-line local safety library.
- Outside-the-box isolation in new prog theories worked: rooted list budget, primitive result contracts and entry shape laws all build independently of broken production exports.
- We were approaching the wrong abstraction when proceeding from primitive result facts directly to whole step_call. Meter preservation on all results and forbidden-error exclusion need one compositional interface; current refined PLAN supplies it.
- Do not optimize termination or the false unrestricted nonempty-context safety theorem. Remaining bottleneck is reachable scoped safety and immediate precompile execution.

### What Went Wrong
- C1.3.6 was too coarse: proceed_call immediately dispatches precompiles after pushing, so whole entry preservation needs precompile contracts before general step_call. E0017 exposed this missing dependency and was accepted only as bounded partial progress.
- Unresolved proceed_call condition produced >4KB goal. Local split fixed the shape boundary; whole-opcode unfolding would repeat the same design failure.
- Simp can discharge scalar subgoals and normalize call_meter_total_cons, destroying irule matches; use verified goals and Excl call_meter_total_cons at list interfaces.
- No vfmCallMeterSafe theorem is verified yet; handoff interrupted immediately after draft write.

### Ignored Signals
- Primitive call_meter_result contracts deliberately establish all-result meters/tail, not forbidden-error exclusion. They cannot replace safety triples without adapters.
- Successful grant transfer increases the pushed pair's claim relative to the depleted parent; compare against the original frame before grant payment, not the intermediate source.
- dispatch_precompiles defaults to Impossible outside its finite address domain; never remove its membership guard.

### Strategy Adjustments
- Reviewed and committed rooted budget infrastructure b7f6ec4c, primitive result/grant contracts 2e6cd255, bounded entry boundaries and refined PLAN 8f24fd3f.
- C1.3.6 now has explicit composition, neutral-adapter, precompile and assembly leaves. C1.3.6.2 is active; only untracked file is the new unbuilt Safe script.
- Keep arbitrary external caller unrestricted and preserve the persisted narrowly amended export contract. Production vfmProgCallScript.sml remains unchanged this session.

### Oracle Feedback
- E0015 accepted exact rooted-prefix/indexed budget and list/state lifting; E0016 accepted all-result primitive contracts plus separate grant exchange.
- E0017 accepted as missing-helper partial evidence, not whole entry proof. Strategist refined C1.3.6 into .1-.5 instead of authorizing large semantic unfolding.
- E0018 accepted only five conditional local entry boundaries. Precompile coverage and whole-step preservation remain separate obligations.

## Evidence Pointers
- episode:E0015 - rooted budget checked and reviewed
- episode:E0016 - primitive meter/grant contracts checked and reviewed
- episode:E0017 - missing compositional/precompile prerequisite, partial entry evidence
- episode:E0018 - bounded entry audit accepted
- tool_output:TO_seq58_progcall_port-20261031T123059Z_m0441_t001 - vfmCallBudgetTheory clean
- tool_output:TO_seq58_progcall_port-20261031T123059Z_m0483_t001 - vfmCallMeterTheory clean
- tool_output:TO_seq58_progcall_port-20261031T123059Z_m0518_t001 - vfmCallEntryTheory clean
- tool_output:TO_seq58_progcall_port-20261031T123059Z_m0515_t001 - refined composition/precompile PLAN
- tool_output:TO_seq58_progcall_port-20261031T123059Z_m0528_t001 - only untracked Safe draft remains
- source:prog/vfmCallMeterSafeScript.sml - unbuilt active draft
