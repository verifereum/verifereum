# DOSSIER: seq58_prog_call_rules

PLAN: `prog/PLAN_seq58_prog_call_rules.md`

## Component Index

| Component | Status | Diagnosis | Latest Episode | Next |
|---|---|---|---|---|
| C1.1 | proved |  | E0001 |  |
| C1.2 | stuck | risk_mismatch | E0002 | Strategist review meter boundary composition/normalization design before further proof work. |
| C1.2.1 | proved |  | E0003 |  |
| C1.2.2 | proved |  | E0004 |  |
| C1.2.3 | proved |  | E0009 |  |
| C1.3.1 | proved |  | E0010 |  |

## C1.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0001`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 26 steps, 25 tools, 5 holbuild, 1,703,015 tok (1,700,309 in, 2,706 out, 1,649,152 cached), 282.0s, $0.2942892

### Attempts / Evidence

- `E0001` (proved, , actual effort: 1 sessions, 1 msgs, 26 steps, 25 tools, 5 holbuild, 1,703,015 tok (1,700,309 in, 2,706 out, 1,649,152 cached), 282.0s, $0.2942892)
  - Audit immutable baseline, full declaration inventory and semantic charge/refund/access signatures -> Baseline and range coverage recorded in prog/CALL_RULES_AUDIT_seq58.md; primary statement matches TASK; Return corrections already exist in source. (`TO_seq58_prog_call_rules-20261030T113558Z_m0006_t001`, `TO_seq58_prog_call_rules-20261030T113558Z_m0007_t001`)
  - Independent symbolic no-spill charge/refill equation and positive pre-existing spill computation -> Probe theory builds without importing unfinished SPEC rules. Both flags covered; positive spill 7 is refunded to execution even after reservoir-only charge. (`TO_seq58_prog_call_rules-20261030T113558Z_m0024_t001`)

### Evidence refs

- `TO_seq58_prog_call_rules-20261030T113558Z_m0024_t001` (use `read_tool_output` for exact output)
- `TO_seq58_prog_call_rules-20261030T113558Z_m0027_t001` (use `read_tool_output` for exact output)

## C1.2

### Current Status

- result: `stuck`
- diagnosis: `risk_mismatch`
- latest episode: `E0002`
- blocker: Access and delegation segments validated, but full prefix composition and meter segment not validated; broad normalization times out and staged charge leaves nested monadic continuation requiring better boundary interface.
- actual effort: 1 sessions, 1 msgs, 26 steps, 25 tools, 10 holbuild, 2,347,821 tok (2,343,227 in, 4,594 out, 2,307,328 cached), 568.7s, $0.3484708
- next: Strategist review meter boundary composition/normalization design before further proof work.

### Attempts / Evidence

- `E0002` (stuck, risk_mismatch, actual effort: 1 sessions, 1 msgs, 26 steps, 25 tools, 10 holbuild, 2,347,821 tok (2,343,227 in, 4,594 out, 2,307,328 cached), 568.7s, $0.3484708)
  - Independent call_delegate_segment and call_access_segment equations -> Both build clean with explicit rollback/msdomain fields and delegate_check case split. (`TO_seq58_prog_call_rules-20261030T113558Z_m0043_t001`)
  - Straight-line call_meter_segment with generic baseCost, charged/static flags, expansion, grant and sender lookup -> Full simp timed out twice even replacing raw ADD_COMM with AC. Switched to staged first charge then existing no-spill boundary. (`TO_seq58_prog_call_rules-20261030T113558Z_m0047_t001`, `TO_seq58_prog_call_rules-20261030T113558Z_m0049_t001`)
  - Peel initial consume_gas and charge_new_account_apply, then normalize static flag and arithmetic -> First two stages work; gvs[AC ADD_ASSOC ADD_COMM] times out over nested residual continuation. Removed unfinished meter experiment, retaining independently build-clean access boundaries. (`TO_seq58_prog_call_rules-20261030T113558Z_m0054_t001`, `TO_seq58_prog_call_rules-20261030T113558Z_m0056_t001`, `TO_seq58_prog_call_rules-20261030T113558Z_m0058_t001`)

### Evidence refs

- `TO_seq58_prog_call_rules-20261030T113558Z_m0054_t001` (use `read_tool_output` for exact output)
- `TO_seq58_prog_call_rules-20261030T113558Z_m0056_t001` (use `read_tool_output` for exact output)
- `TO_seq58_prog_call_rules-20261030T113558Z_m0058_t001` (use `read_tool_output` for exact output)

## C1.2.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0003`
- blocker: 
- actual effort: 1 sessions, 3 steps, 2 tools, 1 holbuild, 312,582 tok (311,875 in, 707 out, 306,688 cached), 35.5s, $0.0481128

### Attempts / Evidence

- `E0003` (proved, , actual effort: 1 sessions, 3 steps, 2 tools, 1 holbuild, 312,582 tok (311,875 in, 707 out, 306,688 cached), 35.5s, $0.0481128)
  - Single-operation application equalities for consume_gas, optional static assertion, expansion, gas-left and callee lookup -> All five short equations build clean independently; arithmetic guard normalized before consumption proof. Existing charge and access/delegate equations remain build clean. (`TO_seq58_prog_call_rules-20261030T113558Z_m0065_t001`)

### Evidence refs

- `TO_seq58_prog_call_rules-20261030T113558Z_m0065_t001` (use `read_tool_output` for exact output)

## C1.2.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0004`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 14 steps, 13 tools, 6 holbuild, 1,585,530 tok (1,581,799 in, 3,731 out, 1,555,584 cached), 223.8s, $0.2452984

### Attempts / Evidence

- `E0004` (proved, , actual effort: 1 sessions, 1 msgs, 14 steps, 13 tools, 6 holbuild, 1,585,530 tok (1,581,799 in, 3,731 out, 1,555,584 cached), 223.8s, $0.2452984)
  - Compose with explicit intermediate application equations instead of rewriting RHS-only schematic operation lemmas -> call_meter_segment now builds clean: derive base charge, no-spill charge, static check, expansion, gas-left, dynamic charge and sender lookup in order; abbreviate head contexts for record-update matching. Only a scalar call_gas addition-order fact uses metis_tac[ADD_COMM]. (`TO_seq58_prog_call_rules-20261030T113558Z_m0083_t001`)

### Evidence refs

- `TO_seq58_prog_call_rules-20261030T113558Z_m0083_t001` (use `read_tool_output` for exact output)

## C1.2.3

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0009`
- blocker: 
- actual effort: 2 sessions, 2 msgs, 36 steps, 35 tools, 15 holbuild, 2,585,795 tok (2,580,724 in, 5,071 out, 2,436,352 cached), 3647.2s, $0.5830892

### Attempts / Evidence

- `E0005` (progressed, other, actual effort: 1 sessions, 1 msgs, 8 steps, 7 tools, 1 holbuild, 987,621 tok (985,996 in, 1,625 out, 971,520 cached), 82.4s, $0.1423540)
  - Validate stack-pop boundary and mirror existing memory-info boundary for actual CALL-spine composition -> Independent prefix probe builds clean, including prior access/meter composition and new pop/memory-info application equations. Actual step_call prefix theorem remains to be stated/proved. (`TO_seq58_prog_call_rules-20261030T113558Z_m0095_t001`)
- `E0006` (stuck, risk_mismatch, actual effort: 1 sessions, 1 msgs, 15 steps, 14 tools, 4 holbuild, 904,438 tok (902,375 in, 2,063 out, 872,960 cached), 300.4s, $0.1667560)
  - Regroup actual step_call into existing access and meter segments, then simp[step_call_def,ignore_bind_def,bind_assoc] -> Pair binding in source versus returned tuple destructuring in segments leaves nonidentical continuation lambdas; no semantic counterexample indicated. (`TO_seq58_prog_call_rules-20261030T113558Z_m0113_t001`)
  - Add UNCURRY_DEF in simp, then separately pure_rewrite UNCURRY_DEF -> Both leave paired lambda form unchanged/reconstructed by final simp. Three attempts terminated; experimental theorem removed. (`TO_seq58_prog_call_rules-20261030T113558Z_m0115_t001`, `TO_seq58_prog_call_rules-20261030T113558Z_m0117_t001`)
- `E0007` (stuck, risk_mismatch, actual effort: 1 sessions, 2 msgs, 31 steps, 30 tools, 12 holbuild, 2,654,369 tok (2,649,136 in, 5,233 out, 2,582,272 cached), 623.5s, $0.4442852)
  - Prove paired application and function equalities, then restricted simp_tac pure_ss structural reassociation, BETA_TAC and REFL_TAC -> step_call_segments builds clean. Paired function normalization required as well as application normalization; pure_ss needed explicit REFL_TAC. (`TO_seq58_prog_call_rules-20261030T113558Z_m0136_t001`)
  - State actual concrete prefix, derive pop_stack using stack=args++rest, rewrite actual segmented spine, normalize named scalar arguments -> Pop application proved, but bool_ss/std_ss leave constructor cases unreduced. srw_ss reduces them but ambient bind_assoc destroys segment grouping; broad rewrite reconstructs lets and all continuation details. Removed unfinished concrete prefix after bounded attempts, retained checked structural lemma. (`TO_seq58_prog_call_rules-20261030T113558Z_m0145_t001`, `TO_seq58_prog_call_rules-20261030T113558Z_m0149_t001`)
- `E0008` (stuck, risk_mismatch, actual effort: 1 sessions, 2 msgs, 28 steps, 27 tools, 11 holbuild, 3,188,496 tok (3,182,612 in, 5,884 out, 3,140,864 cached), 913.3s, $0.4564224)
  - Opaque access/meter program wrappers and applications, call_prefix_prog wrapper, actual step_call_prefix_bridge -> All build clean, and actual step_call matches named arbitrary-continuation prefix. Concrete prefix evaluation still absent. (`TO_seq58_prog_call_rules-20261030T113558Z_m0173_t001`, `TO_seq58_prog_call_rules-20261030T113558Z_m0187_t001`)
  - Derive pop success then drule call_bind_success and rewrite derived universal continuation equality -> No rewrite of outer prefix bind. Inspection prints monad_bind in derived transport. Qualified vfmExecution$bind and annotated prefix result type, still no match. Removed unfinished application theorem, retained checked wrappers/bridge. (`TO_seq58_prog_call_rules-20261030T113558Z_m0177_t001`, `TO_seq58_prog_call_rules-20261030T113558Z_m0185_t001`)
- `E0009` (proved, , actual effort: 2 sessions, 2 msgs, 36 steps, 35 tools, 15 holbuild, 2,585,795 tok (2,580,724 in, 5,071 out, 2,436,352 cached), 3647.2s, $0.5830892)
  - Typed opaque continuation diagnostic via backward irule call_bind_success and call_pop_stack_apply -> call_pop_bind_apply builds with actual stack type (256 word) list. No forward polymorphic specialization needed. (`TO_seq58_prog_call_rules-20261030T113558Z_m0209_t001`)
  - Compose opaque prefix by pop transport, restricted memory/access bind reductions, matched meter equation and record normalization -> call_prefix_prog_apply proved for arbitrary cont, all 6+vo operands and explicit final gas/memory/stateGasLeft/context/domain updates. Frozen rules untouched. Explicit pair_case_thm and sum_case_def were needed with std_ss; final srw_ss without assumptions avoids operand-name expansion. (`TO_seq58_prog_call_rules-20261030T133624Z_m0236_t001`)

### Evidence refs

- `TO_seq58_prog_call_rules-20261030T113558Z_m0209_t001` (use `read_tool_output` for exact output)
- `TO_seq58_prog_call_rules-20261030T133624Z_m0236_t001` (use `read_tool_output` for exact output)

## C1.3.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0010`
- blocker: 
- actual effort: 1 sessions, 5 steps, 4 tools, 1 holbuild, 489,589 tok (488,991 in, 598 out, 479,232 cached), 150.5s, $0.0734212

### Attempts / Evidence

- `E0010` (proved, , actual effort: 1 sessions, 5 steps, 4 tools, 1 holbuild, 489,589 tok (488,991 in, 598 out, 479,232 cached), 150.5s, $0.0734212)
  - Explicit conditional cost/back interface, isolate MIN bound and reservoir cancellation; charged flag split with single-context primitive reductions -> call_refund_unuse_apply proves exact gasUsed, stateGasLeft and stateGasSpilled updates with arbitrary pre-existing spill. Independent probe theory builds clean. (`TO_seq58_prog_call_rules-20261030T133624Z_m0248_t001`)

### Evidence refs

- `TO_seq58_prog_call_rules-20261030T133624Z_m0248_t001` (use `read_tool_output` for exact output)
