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
| C1.3.2 | progressed | missing_helper | E0011 | Strategist classify checked subset and explicitly assign remaining frozen composition to C2; decide needed bounded handler probes for Invalid and SELFDESTRUCT. No frozen proof edits yet. |
| C1.3.2.1 | proved |  | E0013 |  |
| C1.3.2.2 | proved |  | E0014 |  |
| C1.3.2.3 | proved |  | E0015 |  |
| C2.1 | progressed | missing_helper | E0016 | Request strategist scoped integration guidance: copy validated local helpers into main, or authorize independent theory exports plus constant transport; preserve frozen constants/statements. |
| C2.1.1 | proved |  | E0018 |  |
| C2.1.2 | proved |  | E0023 |  |
| C2.1.3 | proved |  | E0020 |  |
| C2.2 | proved |  | E0026 |  |

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

## C1.3.2

### Current Status

- result: `progressed`
- diagnosis: `missing_helper`
- latest episode: `E0011`
- blocker: Full step_precompile_success_exact depends on frozen step_call_prepared, creating phase circularity. No inventoried independent full failure-handler boundary for Invalid, nor general Code/refund success handler for SELFDESTRUCT. PLAN requires refinement before declaring machinery complete.
- actual effort: 1 sessions, 1 msgs, 15 steps, 14 tools, 2 holbuild, 1,713,181 tok (1,708,924 in, 4,257 out, 1,670,272 cached), 444.0s, $0.2869012
- next: Strategist classify checked subset and explicitly assign remaining frozen composition to C2; decide needed bounded handler probes for Invalid and SELFDESTRUCT. No frozen proof edits yet.

### Attempts / Evidence

- `E0011` (progressed, missing_helper, actual effort: 1 sessions, 1 msgs, 15 steps, 14 tools, 2 holbuild, 1,713,181 tok (1,708,924 in, 4,257 out, 1,670,272 cached), 444.0s, $0.2869012)
  - Extract dependency-closed tail helper subset into independent vfmProgCallTailProbeTheory; locate handler helper origin and inspect Invalid/SELFDESTRUCT consumers -> Nine local helpers build independently. Precompile proceed helper initially failed at context abbreviation because get_accounts was opaque; adding get_accounts_def in copied proof closes it. handle_create_not_none, exact successful Memory handler, repay/absorb fields and restore arithmetic all checked. Audit records remaining coverage gaps. (`TO_seq58_prog_call_rules-20261030T133624Z_m0264_t001`, `TO_seq58_prog_call_rules-20261030T133624Z_m0266_t001`)

### Evidence refs

- `TO_seq58_prog_call_rules-20261030T133624Z_m0266_t001` (use `read_tool_output` for exact output)
- `TO_seq58_prog_call_rules-20261030T133624Z_m0267_t001` (use `read_tool_output` for exact output)
- `TO_seq58_prog_call_rules-20261030T133624Z_m0262_t001` (use `read_tool_output` for exact output)

## C1.3.2.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0013`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 28 steps, 27 tools, 7 holbuild, 1,776,807 tok (1,774,073 in, 2,734 out, 1,737,600 cached), 2055.3s, $0.2740460

### Attempts / Evidence

- `E0012` (progressed, wrong_statement, actual effort: 1 sessions, 1 msgs, 11 steps, 10 tools, 1 holbuild, 1,480,698 tok (1,479,576 in, 1,122 out, 1,329,024 cached), 122.5s, $0.4452264)
  - State proposed outermost Invalid handler equality with only singleton contexts; reduce handle_create_not_none then restore/forfeit operations -> Residual guard requires c.gasUsed - c.stateGasSpilled <= c.msgParams.gasLimit; without any child meter bound consume_gas fails on malformed contexts. This is missing helper premise, not evidence against frozen SPEC rules (which have wf_state). Removed unfinished theorem; checked nine-helper tail subset remains. (`TO_seq58_prog_call_rules-20261030T133624Z_m0278_t001`, `TO_seq58_prog_call_rules-20261030T133624Z_m0280_t001`)
- `E0013` (proved, , actual effort: 1 sessions, 1 msgs, 28 steps, 27 tools, 7 holbuild, 1,776,807 tok (1,774,073 in, 2,734 out, 1,737,600 cached), 2055.3s, $0.2740460)
  - Rebuild and commit independent nine-helper tail subset; add corrected singleton Invalid equality with restored child meter bound. -> Subset committed 332bc979; outermost equality builds by separate forfeiture arithmetic then handler reduction. (`TO_seq58_prog_call_rules-20261030T133624Z_m0288_t001`, `TO_seq58_prog_call_rules-20261030T133624Z_m0296_t001`)
  - Prove inner Invalid equality for both output destinations and account-charge flags; independently copy existing context refill definition. -> Checked exact settlement with no parent gas bound. Final simplification uses stack_limit_def and AC addition; wf_context child gas bound implies new helper premise. Frozen statements untouched; audit updated. (`TO_seq58_prog_call_rules-20261030T133624Z_m0311_t001`, `TO_seq58_prog_call_rules-20261030T133624Z_m0313_t001`)

### Evidence refs

- `TO_seq58_prog_call_rules-20261030T133624Z_m0311_t001` (use `read_tool_output` for exact output)
- `TO_seq58_prog_call_rules-20261030T133624Z_m0314_t001` (use `read_tool_output` for exact output)

## C1.3.2.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0014`
- blocker: 
- actual effort: 1 sessions, 4 steps, 3 tools, 1 holbuild, 309,323 tok (307,962 in, 1,361 out, 302,976 cached), 50.6s, $0.0538796

### Attempts / Evidence

- `E0014` (proved, , actual effort: 1 sessions, 4 steps, 3 tools, 1 holbuild, 309,323 tok (307,962 in, 1,361 out, 302,976 cached), 50.6s, $0.0538796)
  - Direct operation reduction for singleton success and inner Memory/Code success with arbitrary refunds. -> All three exact handle_exception NONE equalities build; no deposit conflation, no frozen statement edits. Audit updated. (`TO_seq58_prog_call_rules-20261030T133624Z_m0322_t001`)

### Evidence refs

- `TO_seq58_prog_call_rules-20261030T133624Z_m0322_t001` (use `read_tool_output` for exact output)
- `TO_seq58_prog_call_rules-20261030T133624Z_m0323_t001` (use `read_tool_output` for exact output)

## C1.3.2.3

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0015`
- blocker: 
- actual effort: 1 sessions, 2 msgs, 25 steps, 24 tools, 8 holbuild, 2,221,338 tok (2,218,511 in, 2,827 out, 2,180,736 cached), 316.8s, $0.3218936

### Attempts / Evidence

- `E0015` (proved, , actual effort: 1 sessions, 2 msgs, 25 steps, 24 tools, 8 holbuild, 2,221,338 tok (2,218,511 in, 2,827 out, 2,180,736 cached), 316.8s, $0.3218936)
  - Check empty Memory/Code deposit operational equations and factor handle_step through successful settlement. -> All four new local helpers build. Code explicitly updates account code to [] and assumes child used<=limit; Memory is unchanged. Unit result annotation prevents unconstrained polymorphic reraise mismatch in composition. (`TO_seq58_prog_call_rules-20261030T133624Z_m0350_t001`)
  - Inspect SELFDESTRUCT semantics/frozen consumers and map tail coverage. -> Semantics clears returnData before gas charge; frozen execution and reservoir bounds supply zero-charge deposit guard. Audit maps Invalid, SELFDESTRUCT and precompile boundaries, explicitly deferring step_precompile_success_exact to C2. (`TO_seq58_prog_call_rules-20261030T133624Z_m0337_t001`, `TO_seq58_prog_call_rules-20261030T133624Z_m0352_t001`, `TO_seq58_prog_call_rules-20261030T133624Z_m0353_t001`)

### Evidence refs

- `TO_seq58_prog_call_rules-20261030T133624Z_m0350_t001` (use `read_tool_output` for exact output)
- `TO_seq58_prog_call_rules-20261030T133624Z_m0353_t001` (use `read_tool_output` for exact output)

## C2.1

### Current Status

- result: `progressed`
- diagnosis: `missing_helper`
- latest episode: `E0016`
- blocker: Main-theory source transfer/packaging of independently validated local prefix machinery not yet performed.
- actual effort: 1 sessions, 1 msgs, 6 steps, 5 tools, 619,575 tok (618,873 in, 702 out, 604,160 cached), 55.5s, $0.0968620
- next: Request strategist scoped integration guidance: copy validated local helpers into main, or authorize independent theory exports plus constant transport; preserve frozen constants/statements.

### Attempts / Evidence

- `E0016` (progressed, missing_helper, actual effort: 1 sessions, 1 msgs, 6 steps, 5 tools, 619,575 tok (618,873 in, 702 out, 604,160 cached), 55.5s, $0.0968620)
  - Inspect frozen balance/depth proof integration sites and checked prefix/refund interfaces before editing. -> Validated prefix/refund remain only local declarations in independent probe; main theory has none. Probe also duplicates five prog boundary constants, so simply importing its exported lemma would not match frozen main constants. Need explicit authorized source transfer or shared packaging before using prefix in frozen proofs; no frozen body edited. (`TO_seq58_prog_call_rules-20261030T133624Z_m0363_t001`, `TO_seq58_prog_call_rules-20261030T133624Z_m0364_t001`, `TO_seq58_prog_call_rules-20261030T133624Z_m0365_t001`)

### Evidence refs

- `TO_seq58_prog_call_rules-20261030T133624Z_m0364_t001` (use `read_tool_output` for exact output)
- `TO_seq58_prog_call_rules-20261030T133624Z_m0365_t001` (use `read_tool_output` for exact output)

## C2.1.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0018`
- blocker: 
- actual effort: 1 sessions, 3 steps, 2 tools, 1 holbuild, 158,927 tok (158,659 in, 268 out, 151,296 cached), 279.2s, $0.0325356

### Attempts / Evidence

- `E0017` (progressed, other, actual effort: 1 sessions, 2 msgs, 23 steps, 22 tools, 2 holbuild, 2,845,057 tok (2,835,938 in, 9,119 out, 2,646,144 cached), 525.9s, $0.7353924)
  - Inventory matching native boundaries and transfer missing local dependency closure before SPEC_Call_fail_balance. -> Reused main access_address_split, charge_new_account_apply, memory_expansion_info_split and original definitions. First transferred subset through call_pop_stack_apply checks; native meter proof needed explicit call_gas stipend normalization because main imports call_gas_zero_cost[simp]. Whole build then reached pre-existing SPEC_Call_fail_depth failure. Subsequently transferred remaining block through call_refund_unuse_apply, not yet built at forced handoff. (`TO_seq58_prog_call_rules-20261030T133624Z_m0385_t001`, `TO_seq58_prog_call_rules-20261030T133624Z_m0387_t001`, `TO_seq58_prog_call_rules-20261030T133624Z_m0388_t001`)
- `E0018` (proved, , actual effort: 1 sessions, 3 steps, 2 tools, 1 holbuild, 158,927 tok (158,659 in, 268 out, 151,296 cached), 279.2s, $0.0325356)
  - Build native transferred prefix/refund helper block in vfmProgTheory and inspect explicit theorem acceptance. -> All transferred helpers including step_call_prefix_bridge, call_prefix_prog_apply, call_refund_unuse_apply accepted. Whole build reaches unchanged pre-existing depth proof failure. (`TO_seq58_prog_call_rules-20261030T133624Z_m0395_t001`, `TO_seq58_prog_call_rules-20261030T133624Z_m0396_t001`)

### Evidence refs

- `TO_seq58_prog_call_rules-20261030T133624Z_m0396_t001` (use `read_tool_output` for exact output)

## C2.1.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0023`
- blocker: 
- actual effort: 1 sessions, 7 steps, 6 tools, 3 holbuild, 397,134 tok (396,516 in, 618 out, 378,368 cached), 62.0s, $0.0803128

### Attempts / Evidence

- `E0019` (stuck, risk_mismatch, actual effort: 1 sessions, 2 msgs, 18 steps, 17 tools, 7 holbuild, 1,310,542 tok (1,307,316 in, 3,226 out, 1,259,136 cached), 340.5s, $0.2545336)
  - Expose step_call through IMP_EVM_SPEC then step_call_prefix_bridge. -> Verified entry prefix; required moving the exact step case equation to goal and peeling ignore_bind then bind (not complete step_call). Continuation and c/k/cs now abbreviated. (`TO_seq58_prog_call_rules-20261030T133624Z_m0415_t001`)
  - irule call_prefix_prog_apply on explicit expected charged-state equality; then normalize field aliases and specialize vo=1. -> Repeated No match, including SPEC_ALL/Q.INST vo=1/SIMP_RULE std_ss. This interface forces a large copied output equality before even producing premises; no semantic counterexample observed. Stop instead of further theorem plumbing. (`TO_seq58_prog_call_rules-20261030T133624Z_m0418_t001`, `TO_seq58_prog_call_rules-20261030T133624Z_m0420_t001`)
- `E0021` (progressed, other, actual effort: 1 sessions, 2 msgs, 23 steps, 22 tools, 6 holbuild, 2,640,792 tok (2,638,857 in, 1,935 out, 2,596,352 cached), 215.0s, $0.3639952)
  - Apply result adapter then native credit_new_account_apply; normalize credit context, execute abort_call_value and finish frame with end_tac. -> SPEC_Call_fail_balance now checks without cheat or statement changes. Build reaches unchanged SPEC_Call_fail_depth. Adjacent credit+unuse helper not applicable because abort pushes stack/sets returnData between them, so used already validated credit_new_account_apply and explicit refund arithmetic. (`TO_seq58_prog_call_rules-20261030T133624Z_m0467_t001`)
- `E0022` (progressed, other, actual effort: 1 sessions, 4 msgs, 40 steps, 39 tools, 9 holbuild, 4,884,446 tok (4,880,212 in, 4,234 out, 4,671,360 cached), 371.1s, $0.9271800)
  - Port checked balance entry/prefix adapter pattern to depth with general vOff and existing cs. -> Depth entry checks; adapter witnesses and simplification reduce entire charged-state equality to call_gas equation whose argument differs by AC addition only. Last edit adds the checked narrow AC closure used in balance; not yet built due forced handoff. (`TO_seq58_prog_call_rules-20261030T133624Z_m0478_t001`, `TO_seq58_prog_call_rules-20261030T133624Z_m0480_t001`, `TO_seq58_prog_call_rules-20261030T133624Z_m0484_t001`)
- `E0023` (proved, , actual effort: 1 sessions, 7 steps, 6 tools, 3 holbuild, 397,134 tok (396,516 in, 618 out, 378,368 cached), 62.0s, $0.0803128)
  - Reuse result adapter for depth; reduce return-data/depth continuation then credit_new_account_apply, refund arithmetic and abort_unuse frame finish. -> Both frozen failure rules check; whole target proceeds to existing SPEC_Call failure. (`TO_seq58_prog_call_rules-20261030T133624Z_m0494_t001`)

### Evidence refs

- `TO_seq58_prog_call_rules-20261030T133624Z_m0494_t001` (use `read_tool_output` for exact output)

## C2.1.3

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0020`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 18 steps, 17 tools, 7 holbuild, 1,724,017 tok (1,721,537 in, 2,480 out, 1,685,888 cached), 322.3s, $0.2646868

### Attempts / Evidence

- `E0020` (proved, , actual effort: 1 sessions, 1 msgs, 18 steps, 17 tools, 7 holbuild, 1,724,017 tok (1,721,537 in, 2,480 out, 1,685,888 cached), 322.3s, $0.2646868)
  - Result-variable adapter via drule_all native theorem, qspec cont, gvs; validate in charged-state subgoal of balance rule. -> Adapter checks and balance charged-state equality fully proved with explicit antecedent witnesses, targeted aliases and EL_TAKE. Final residual call_gas argument differs only by AC addition, closed by moving call_gas assumption and simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]. Build reaches subsequent prefix-applied probe with equality in context. (`TO_seq58_prog_call_rules-20261030T133624Z_m0442_t001`)
  - Unconstrained metis adapter proof and global gvs AC closure. -> Each timed out; replaced by controlled forward theorem application and narrow bool_ss normalization; neither remains in source. (`TO_seq58_prog_call_rules-20261030T133624Z_m0430_t001`, `TO_seq58_prog_call_rules-20261030T133624Z_m0438_t001`)

### Evidence refs

- `TO_seq58_prog_call_rules-20261030T133624Z_m0442_t001` (use `read_tool_output` for exact output)

## C2.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0026`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 13 steps, 12 tools, 5 holbuild, 1,642,927 tok (1,641,201 in, 1,726 out, 1,614,720 cached), 146.2s, $0.2316940

### Attempts / Evidence

- `E0024` (progressed, other, actual effort: 2 sessions, 2 msgs, 40 steps, 39 tools, 10 holbuild, 3,507,236 tok (3,503,365 in, 3,871 out, 3,332,992 cached), 595.2s, $0.7127552)
  - Port depth prefix-result application into SPEC_Call and retain proceed_call/frame tail; remove obsolete delegation residual branches. -> SPEC_Call now checks; call_gas_cost_covers_stipend checks after explicit MIN case split; build reaches existing step_call_prepared proof failure. (`TO_seq58_prog_call_rules-20261030T153638Z_m0538_t001`)
- `E0025` (stuck, risk_mismatch, actual effort: 2 sessions, 3 msgs, 55 steps, 54 tools, 16 holbuild, 5,171,581 tok (5,164,687 in, 6,894 out, 4,968,576 cached), 1059.6s, $0.9580196)
  - Reuse prefix adapter and successful continuation in SPEC_Call; remove old delegation result plumbing and update frame branch order. -> SPEC_Call fully checks; stipend cost helper checks after MIN split. Build reaches step_call_prepared. (`TO_seq58_prog_call_rules-20261030T153638Z_m0538_t001`)
  - Replace prepared proof's obsolete semantic expansion with prefix adapter; simp/fs/gvs aliases then isolate call_gas and bound for narrow AC. -> Adapter witnesses accepted, but simplification yields 4 alias-expanded leaves. Global fs AC timed out; narrow AC plus decide_tac/ARITH_TAC failed on nested-if cost bound. Need better normalization of prepared theorem's explicit equalities rather than consumer aliases. (`TO_seq58_prog_call_rules-20261030T153638Z_m0548_t001`, `TO_seq58_prog_call_rules-20261030T153638Z_m0554_t001`)
- `E0026` (proved, , actual effort: 1 sessions, 1 msgs, 13 steps, 12 tools, 5 holbuild, 1,642,927 tok (1,641,201 in, 1,726 out, 1,614,720 cached), 146.2s, $0.2316940)
  - Introduce local elementary base-cost bound; derive before alias expansion, then gvs EL_TAKE and split call_has_value for stack selectors. Normalize final continuation assumptions together with goal via gvs. -> SPEC_Call, all intervening helpers, and step_call_prepared check. Build advances to proceed_call_precompile_success_meter, outside this component. (`TO_seq58_prog_call_rules-20261030T153638Z_m0571_t001`)

### Evidence refs

- `TO_seq58_prog_call_rules-20261030T153638Z_m0571_t001` (use `read_tool_output` for exact output)
