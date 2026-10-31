# STATE_seq58_progcall_port
Updated: 2026-10-31

## Cursor
- component: C1.3.8
- status: in_progress
- active_file: prog/vfmCallInnerScript.sml
- next_action: Begin C1.3.8 and verify vfmCallInnerTheory. Then prove the pop_and_incorporate_context budget boundary: inspect existing exact pair equation at prog/vfmProgCallScript.sml:369-404 and scalar success_pop_backed/claim, failure_credit_backed in vfmCallMeterProbeScript.sml. Use budget_parent_margin for internal pop and budget_root_exit for root pop; keep actual credit-after-absorb ordering. handle_create fixed-tail interface is already checked at Inner:1080.
- expected_goal_shape: Internal pop: budget n ceiling s, n < LENGTH s.contexts, child::parent::rest and parent wf imply settled merged head backed and claim <= child claim + parent claim; root pop discharges budget by length. Later compose restore/forfeit, output operations and handle_step.
- verify_with: holbuild(targets=["vfmCallInnerTheory"], timeout=1800)

## If This Fails
- Inspect exact semantic result before expanding arithmetic. checkpoint_progress for useful partial boundaries; if scalar/list interface is structurally insufficient, close_component(stuck) with evidence then request strategist review, rather than adding exported hypotheses.

## Do Not Retry
- Force stack-extending CALL/CREATE or stack-shrinking pop through fixed-tail call_meter_result.: Fixed-tail abstraction intentionally excludes frame stack changes; use budget-level entry/pop contracts.
  - evidence: episode:E0039
  - evidence: source:prog/vfmCallStepsScript.sml
- Use simp[call_meter_safe_def,...invariant contracts...] uniformly across conditional return/nontrivial operations.: Definition unfolding may prevent interface rewrites and expose irrelevant primitive executions; split trivial cases before unfolding.
  - evidence: tool_output:TO_seq58_progcall_port-20261031T152132Z_m1157_t001
  - evidence: tool_output:TO_seq58_progcall_port-20261031T152132Z_m1159_t001

## Reflection
### Tunnel Vision Check
- Fixed-tail family interfaces worked for every ordinary constructor and code deposit. The next theorem changes stack shape, so do not optimize another fixed-tail adapter for pop.
- Outside-the-box option: expose a context-valued settlement boundary once and use budget_pop/root_exit instead of monad-unfolding throughout handle_exception. Existing exact pair equation in ProgCall is a starting point, not a reason to duplicate large unfolds in consumers.
- Fresh expert should first check whether handler intermediate states retain the needed parent wf gas bound and stack room; inner execution's budget theorem alone does not provide these.
- PLAN abstraction remains appropriate: scalar meter laws, list budget boundaries, then semantic handler composition. Escalate if these boundaries cannot cover failure-credit settlement.

### What Went Wrong
- simp with call_meter_safe_def in the same list as invariant rewrites unfolded nontrivial branch contracts before their rewrites matched; split trivial return cases first (storage family).
- Dispatch originally simplified only conclusions, leaving is_call Stop assumptions and 88 cases for metis; gvs on constructor assumptions eliminated non-call cases and removed timeout.
- Higher-order matching was required for update_gas_refund's nested record update. Plain irule did not infer its context transformer.
- Budget lift needed the explicit n <= LENGTH s.contexts fact after context-list splitting; syntactically normalized SUC length was insufficient for drule_all.

### Ignored Signals
- Do not infer generalized variable order: drule ordinary_inst produced forall rest rb c, not c rb rest. Inspect the actual quantified goal before specialization.
- A timeout in dispatch was a normalization bug, not evidence that the opcode family decomposition failed.

### Strategy Adjustments
- Read/copy/log, storage, terminal and opcode/inner execution families are all proved and reviewed; stable commits 3deeafc6, 70d4667a, 3241a41a, 9bf83f83.
- C1.3.8 code-deposit portion is checked and committed d763c671; episode E0040 records nonterminal progress. No handler-pop proof has yet been attempted.
- All source currently builds as vfmCallInnerTheory; task-wide exported rules are not yet complete. Keep modifications under prog/.

### Oracle Feedback
- Reviews E0036-E0039 accepted all family and dispatch proofs without PLAN changes. In particular CALL PC no-op versus ordinary fixed-tail PC composition was validated.
- Current handler component is authorized and active; no need to ask the oracle merely because ancestor risks remain high.

## Evidence Pointers
- episode:E0039 - opcode and inner-execution budget contract proved and reviewed
- episode:E0040 - partial handler component: code-deposit all-result safety
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1204_t001 - inner budget theorem build
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1219_t001 - handle_create interface build
- tool_output:TO_seq58_progcall_port-20261031T152132Z_m1226_t001 - stable deposit commit d763c671
- source:prog/vfmCallBudgetScript.sml:196-245 - pop, root exit and parent margin interfaces
- source:prog/vfmCallMeterProbeScript.sml:219-245 - success and failure backing scalar laws
- source:prog/vfmProgCallScript.sml:369-404 - exact semantic pop settlement equation
