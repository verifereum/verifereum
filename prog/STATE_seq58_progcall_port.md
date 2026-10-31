# STATE_seq58_progcall_port
Updated: 2026-10-31

## Cursor
- component: C1.3.8.2
- status: in_progress
- active_file: prog/vfmCallInnerScript.sml
- next_action: Begin C1.3.8.2, verify vfmCallInnerTheory, then compose handle_exception's prepare prefix (Inner:1162), reader operations, pop budget boundaries (Inner:1094-1124), and safe_exception_output (Inner:1309). First inspect pop_and_incorporate_context/unuse_gas failure ordering: root budget should discharge on all pop results, even without an external caller gas bound. Internal pop already has INL and budget from parent margin.
- expected_goal_shape: wf_state s, budget n ceiling s, 2<=n<=LENGTH contexts and handle_exception e s=(r,t) imply budget n ceiling t. Preparation supplies fixed-tail call_meter_result, internal pop uses preserved parent gas bound; root-pop failure may already have shortened contexts. Output safety preserves budget/nonempty without caller backing. Then compose handle_step and step.
- verify_with: holbuild(targets=["vfmCallInnerTheory"], timeout=1800)

## If This Fails
- Use checked interfaces, not merged-record expansion. checkpoint_progress for partial handler evidence; close_component(stuck) and strategist review only for structural failure. Do not add exported caller backing or extra gas hypotheses.

## Do Not Retry
- Unfold settled merged-record abbreviation with backed/claim/absorb/repay definitions in semantic consumers.: Repeated record normalization times out; call_meter_pop_settle_pair and call_meter_settle_pop_backed/claim now hide the implementation.
  - evidence: episode:E0041
  - evidence: episode:E0042
- Use fixed-tail call_meter_result through stack-shrinking pop or require caller backing after root exit.: The external caller is intentionally unconstrained. Use budget_pop internally and root-exit plus observation budget interfaces externally.
  - evidence: episode:E0043
  - evidence: episode:E0045

## Reflection
### Tunnel Vision Check
- Outside-the-box alternative: prove handler budget preservation for all results separately from forbidden-exception exclusion; root pop can discharge budget even if unuse_gas fails after pop. Check exact ordering before imposing a caller bound.
- The scalar/list/semantic decomposition remains sound: compact settlement made the previously timing-out internal pop proof a short composition.
- A fresh expert should question which wf/stack/gas facts survive handle_create and the preparation prefix, and which root-return nonabort facts belong to later finite-return components. Full handler composition has not been attempted.
- Do not optimize another fixed-tail pop abstraction: root exit deliberately permits an unbacked external caller. Output observation interfaces already handle this.

### What Went Wrong
- Expanding the exact merged settlement record with simp or gvs timed out; E0041 led to the compact settlement interface, now proved and reviewed.
- Automatic functional-update matching failed for generic observation adapters; explicit one-lambda witnesses worked for budget adapters. Safe wrappers then reused those budget facts and primitive result equations.
- Predicate-lambda composition requires ho_match_mp_tac call_meter_safe_ignore_invariant rather than irule. OutputTo constructor order is Memory then Code.
- push_stack simplification normalizes stack_limit to 1024; splitting on the symbolic constant requires gvs[vfmConstantsTheory.stack_limit_def].

### Ignored Signals
- Large repeated merged record expressions were an interface defect, not a reason for more scalar simplification.
- Preservation facts stated via SND of an operation need the pair projection to consume a result equation; metis with pairTheory.SND closed the push nonempty leaf.

### Strategy Adjustments
- C1.3.8.1 completed, reviewed, committed f7852e9c. C1.3.8.2 remains active with partial progress committed b2f6cb27 and ec4298c1.
- Internal/root pop, handle_create budget lifting, exception prepare prefix, and post-pop output safety are checked. Full handle_exception/handle_step/step remain undone.
- Final relevant build vfmCallInnerTheory succeeded; no broken experiments or source cheats were added.

### Oracle Feedback
- E0041 review accepted the abstraction failure and split handler work into compact settlement and semantic integration.
- E0042 review accepted generic settlement/absorption contracts and exact compact pop equation. This insight held in the semantic internal-pop consumer.

## Evidence Pointers
- episode:E0041 - timeout diagnosis and accepted decomposition repair
- episode:E0042 - compact scalar settlement interface proved/reviewed
- episode:E0043 - internal/root pop and handle_create budget lift
- episode:E0044 - exception preparation prefix
- episode:E0045 - post-pop observation and output safety
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1340_t001 - final clean vfmCallInnerTheory build
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1344_t001 - output boundary checkpoint ec4298c1
- source:prog/vfmCallMeterProbeScript.sml:380-501 - compact settle, absorption and exact pop boundary
- source:prog/vfmCallInnerScript.sml:1094-1333 - checked handler building blocks
