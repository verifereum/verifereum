# DOSSIER: seq58_progcall_port

PLAN: `prog/PLAN_seq58_progcall_port.md`

## Component Index

| Component | Status | Diagnosis | Latest Episode | Next |
|---|---|---|---|---|
| C1.1 | proved |  | E0001 |  |
| C1.2 | stuck | risk_mismatch | E0003 | Authorize concrete no-entry CALL probe with gas request 0, value 1, reservoir >=183600, initial gasUsed=0 and spill=183600; creation refund erases execution cost leaving gasUsed=0 before unuse stipend 2300. |
| C1.2.1 | proved |  | E0004 |  |
| C1.2.2 | proved |  | E0009 | Review checked frozen-export obstruction; report unprovable with tightest sufficient repair proposal, without applying it. Candidate repair obligation for no-entry path is calleeGas <= gasUsed after credit (equivalently for positive stipend, MIN stateCost initialSpill + calleeGas <= g+gasCost when charge reservoir-covered). Do not claim this alone repairs every cross-frame path. |
| C1.3 | stuck | wrong_statement | E0011 | Shallow replan C1.3 safety and finite-return infrastructure with internal meter invariant scoped to reachable callee states; never propagate generic spill<=g as unauthorized export premise. Address consumer stack/global-frame invariants explicitly. |
| C1.3.1 | proved |  | E0012 | Review and commit probe. Proceed C1.3.2 nested prefix boundaries; individual frame backing is checked but not yet established adequate for child gas refunds or for internal frame push/pop. |
| C1.3.10 | proved |  | E0050 | Review C1.3.10; commit stable return theory. C1.3.11 must integrate isolated return interfaces and layer stipend observations without leaving duplicate old unrestricted safety machinery. |
| C1.3.11 | proved |  | E0054 | Review C1.3.11; proceed to C1.4 entry normalization and exact context consumer integration. Consider clean auxiliary target only if necessary, rather than claiming full target success. |
| C1.3.2 | proved |  | E0013 | Review bounded nested-frame probes and commit. Then C1.3.3 finite-run strategy checkpoint before authorizing full invariant/finite-return machinery. Remaining integration must prove margin before push (including stipend), ancestor-budget preservation, and exceptional-return restore/forfeit branches. |
| C1.3.3 | proved |  | E0014 | Mandatory scoped PLAN update before accepting parent complete or beginning C1.4: evaluate proposed budget and add executable preservation, safety, collection-return, final-pop/summary and stipend leaves. Commit checked audit/probe changes after review. |
| C1.3.4 | proved |  | E0015 | Review C1.3.4, commit new budget theory with required trailer, then scheduled semantic primitive contracts C1.3.5. |
| C1.3.5 | proved |  | E0016 | Review primitive boundary component, commit stable theory, then scheduled fresh CALL/CREATE push/entry proofs. |
| C1.3.6 | stuck | missing_helper | E0017 | Review scoped missing dependency: preserve entry shape/budget partial work, introduce or assign compositional meter+exception-safety interface and ordinary primitive/precompile laws before whole step_call/step_create, avoiding a flat 1500-line duplicated local safety library. |
| C1.3.6.1 | proved |  | E0018 | Review/commit bounded entry facts, then C1.3.6.2 composition probes. |
| C1.3.6.2 | proved |  | E0019 | Review then commit safe-contract theory; continue scheduled neutral-operation adapters. |
| C1.3.6.3 | proved |  | E0020 | Review adapters then commit; next scheduled precompile preservation. |
| C1.3.6.4 | proved |  | E0021 | Review and commit precompile boundaries, then scheduled whole entry composition. |
| C1.3.6.5 | progressed | missing_helper | E0023 | Request strategist guidance on surplus-preserving composition before unfolding any whole opcode. |
| C1.3.6.5.1 | proved |  | E0024 | Review reservation interface and commit; then reservation acquisition/discharge leaf. |
| C1.3.6.5.2 | proved |  | E0026 |  |
| C1.3.6.5.3 | proved |  | E0030 |  |
| C1.3.6.5.4 | proved |  | E0032 |  |
| C1.3.7 | progressed | other | E0033 | Continue finite opcode coverage with memory/storage/terminal families, then dispatch and step_inner lift. New vfmCallInnerScript.sml is build-clean and untracked until stable checkpoint commit. |
| C1.3.7.1 | proved |  | E0034 |  |
| C1.3.7.2 | proved |  | E0036 | Review and commit read/memory/copy/log family; proceed to scheduled storage family. |
| C1.3.7.3 | proved |  | E0037 | Review and commit storage safety family, then scheduled terminal opcode family. |
| C1.3.7.4 | proved |  | E0038 | Review and commit terminal family; assemble ordinary dispatch and inner execution as scheduled. |
| C1.3.7.5 | proved |  | E0039 | Review and commit dispatch and inner execution; proceed to handler/finite return components. |
| C1.3.8 | stuck | risk_mismatch | E0041 | Review handler decomposition: expose settled-context backing and claim contracts without expanding full context records inside semantic consumer. |
| C1.3.8.1 | proved |  | E0042 |  |
| C1.3.8.2 | proved |  | E0048 | Ancestor review should schedule remaining nonabort/finite-return interface using authorized caller grant bound, not unconditional root safety. |
| C1.3.9 | proved |  | E0049 | Review whether finite-return boundary suffices to close this leaf and schedule replacement/removal of old unrestricted local chain when integrating call_returns_summary. |
| C1.4 | proved |  | E0056 | Review bounded proof and authorize checkpoint commit despite downstream caller_observation_frame failure; proceed to shared frame/export component. |
| C1.5 | proved |  | E0058 | Review bounded C1.5 closure and authorize commit; C1.6 must restate both exports and validate shared tactics against actual new semantic meter relations. |
| C1.6 | progressed | missing_helper | E0059 | Escalate interface quality to strategist rather than add more manual existential instantiations or copy large assumptions. |
| C1.6.1 | proved |  | E0060 | Review bounded closure, authorize checkpoint commit despite known downstream export failure as previous boundaries; C1.6.2 replace experimental tactic with opaque wrapper consumption. |
| C1.6.2 | proved |  | E0062 |  |
| C1.8 | proved |  | E0010 | Review C1.8 and allow C1.3. Note C1.3 call_exn_safe_step_call universally quantifies over merely nonempty contexts, so original checked counterexample still disproves this local helper; exported guard alone does not repair broad helper. Need invariant-specific safety decomposition rather than merely matching current consume_gas goal. Consider shallow C1.3 redesign before execution. |

## C1.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0001`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 25 steps, 24 tools, 5 holbuild, 1,650,987 tok (1,646,392 in, 4,595 out, 1,583,488 cached), 315.2s, $0.5035996

### Attempts / Evidence

- `E0001` (proved, , actual effort: 1 sessions, 1 msgs, 25 steps, 24 tools, 5 holbuild, 1,650,987 tok (1,646,392 in, 4,595 out, 1,583,488 cached), 315.2s, $0.5035996)
  - Add get_accounts/drain getter/setter normalization to step_push_TL_TL CREATE branch. -> Unchanged structural statement checked; build reaches boundary equations. (`TO_seq58_progcall_port-20261030T170049Z_m0014_t001`)
  - Restate proceed_call_pair with charged flag, reservoir, drained parent and incoming transfer log; restate pop/handler equations via absorb/repay or creation credit, restoration before unused gas. -> All five boundary equations checked. Local handler bound now covers restored spill before unuse. Build progresses past boundary and Collect helpers to C1.2 sstore safety failure. (`TO_seq58_progcall_port-20261030T170049Z_m0018_t001`, `TO_seq58_progcall_port-20261030T170049Z_m0022_t001`, `TO_seq58_progcall_port-20261030T170049Z_m0026_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261030T170049Z_m0026_t001` (use `read_tool_output` for exact output)

## C1.2

### Current Status

- result: `stuck`
- diagnosis: `risk_mismatch`
- latest episode: `E0003`
- blocker: call_exn_safe_step_call may be false for arbitrary initial spill: CALL with value, empty account and balance failure credits MIN creation-cost spill from full caller gasUsed before stipend unuse. wf_context does not constrain spill either. Need concrete probe and strategist assessment of frozen exports.
- actual effort: 1 sessions, 2 msgs, 35 steps, 34 tools, 6 holbuild, 3,101,424 tok (3,097,462 in, 3,962 out, 3,045,760 cached), 394.2s, $0.4476000
- next: Authorize concrete no-entry CALL probe with gas request 0, value 1, reservoir >=183600, initial gasUsed=0 and spill=183600; creation refund erases execution cost leaving gasUsed=0 before unuse stipend 2300.

### Attempts / Evidence

- `E0002` (progressed, other, actual effort: 1 sessions, 2 msgs, 34 steps, 33 tools, 6 holbuild, 3,000,283 tok (2,996,680 in, 3,603 out, 2,946,304 cached), 382.9s, $0.4314124)
  - Prove credit/charge/new-account/drain safety at primitive boundary; compose sstore/selfdestruct/proceed safety; cover new DUPN/SWAPN/EXCHANGE opcodes; rewrite CREATE safety for charge before withhold. -> Build verifies all additions and proceeds through call_exn_safe_step_create. Next failure is old step_call consumption spine. (`TO_seq58_progcall_port-20261030T170049Z_m0061_t001`)
- `E0003` (stuck, risk_mismatch, actual effort: 1 sessions, 2 msgs, 35 steps, 34 tools, 6 holbuild, 3,101,424 tok (3,097,462 in, 3,962 out, 3,045,760 cached), 394.2s, $0.4476000)
  - Port primitive safety and opcode consumers; inspect changed CALL spine before adapting old consumed-credit proof. -> Checked prefix through CREATE. Old CALL safety only assumes nonempty contexts, but creation refund can reduce gasUsed below stipend before abort_unuse, because initial spill is unconstrained. This is a structural invariant issue not a tactic failure. (`TO_seq58_progcall_port-20261030T170049Z_m0061_t001`, `TO_seq58_progcall_port-20261030T170049Z_m0062_t001`, `TO_seq58_progcall_port-20261030T170049Z_m0065_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261030T170049Z_m0061_t001` (use `read_tool_output` for exact output)
- `TO_seq58_progcall_port-20261030T170049Z_m0062_t001` (use `read_tool_output` for exact output)
- `TO_seq58_progcall_port-20261030T170049Z_m0065_t001` (use `read_tool_output` for exact output)

## C1.2.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0004`
- blocker: 
- actual effort: 1 sessions, 3 msgs, 35 steps, 34 tools, 11 holbuild, 4,082,776 tok (4,079,550 in, 3,226 out, 4,034,688 cached), 841.2s, $0.5254528

### Attempts / Evidence

- `E0004` (proved, , actual effort: 1 sessions, 3 msgs, 35 steps, 34 tools, 11 holbuild, 4,082,776 tok (4,079,550 in, 3,226 out, 4,034,688 cached), 841.2s, $0.5254528)
  - Standalone prog/vfmCallRefundProbeTheory evaluates concrete CALL with zero gas request, value one, recipient 256, empty accounts, caller used=0/spill=reservoir=183600. -> Checked result INR(SOME Impossible), caller gasUsed/left/spilled all zero, stack [0w] and pc still zero. Exact cost 14300; grant computation (0,2300). Derived falsity of universal nonempty-context CALL safety. No export falsehood claimed yet. (`TO_seq58_progcall_port-20261030T170049Z_m0097_t001`, `TO_seq58_progcall_port-20261030T170049Z_m0105_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261030T170049Z_m0105_t001` (use `read_tool_output` for exact output)

## C1.2.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0009`
- blocker: 
- actual effort: 1 sessions, 3 msgs, 43 steps, 42 tools, 11 holbuild, 2,986,655 tok (2,981,254 in, 5,401 out, 2,917,120 cached), 1017.3s, $0.4739900
- next: Review checked frozen-export obstruction; report unprovable with tightest sufficient repair proposal, without applying it. Candidate repair obligation for no-entry path is calleeGas <= gasUsed after credit (equivalently for positive stipend, MIN stateCost initialSpill + calleeGas <= g+gasCost when charge reservoir-covered). Do not claim this alone repairs every cross-frame path.

### Attempts / Evidence

- `E0005` (progressed, other, actual effort: 1 sessions, 1 msgs, 10 steps, 9 tools, 2 holbuild, 1,350,690 tok (1,349,599 in, 1,091 out, 1,194,496 cached), 293.4s, $0.4405656)
  - Check wf_state for concrete refund probe, then begin relating step to checked step_call result. -> refund_probe_wf proved and standalone build clean. step dispatch lemma first attempt named nonexistent parse_code_aux_def; latest edit replaces it with small EVAL FLOOKUP fact and checked result premises, not yet built; ends with intentional FAIL_TAC. (`TO_seq58_progcall_port-20261030T170049Z_m0114_t001`, `TO_seq58_progcall_port-20261030T170049Z_m0116_t001`, `TO_seq58_progcall_port-20261030T170049Z_m0117_t001`)
- `E0006` (stuck, risk_mismatch, actual effort: 1 sessions, 1 msgs, 20 steps, 19 tools, 4 holbuild, 1,169,029 tok (1,167,433 in, 1,596 out, 1,134,208 cached), 292.7s, $0.1958308)
  - EVAL_TAC FLOOKUP parse_code singleton -> 30s timeout on parse_opcode choice definition. (`TO_seq58_progcall_port-20261030T170049Z_m0124_t001`)
  - simp parse_code with parse_opcode_cond_thm -> 30s timeout; split parse_opcode computation out. (`TO_seq58_progcall_port-20261030T170049Z_m0135_t001`)
  - rewrite parse_opcode_cond_thm then EVAL or word_eq_n2w simp -> Leaves concrete word comparisons / MOD_2EXP_EQ dimindex(:8) unresolved; two goals reported at branch close. Step and SPEC probes remain pending. (`TO_seq58_progcall_port-20261030T170049Z_m0137_t001`, `TO_seq58_progcall_port-20261030T170049Z_m0142_t001`)
- `E0007` (stuck, wrong_statement, actual effort: 1 sessions, 3 msgs, 39 steps, 38 tools, 10 holbuild, 3,199,843 tok (3,196,074 in, 3,769 out, 3,145,600 cached), 994.4s, $0.4531980)
  - Load wordsLib; isolate opcode fact; derive singleton parse_code lookup using FLOOKUP_UPDATE; normalize step via checked Impossible result. -> refund_probe_opcode and refund_probe_step proved. Earlier ground word failures were missing wordsLib computation registration. (`TO_seq58_progcall_port-20261030T170049Z_m0163_t001`)
  - Induct on guarded next-state FUNPOW -> refund_probe_next_iterates proved: after positive steps exception always SOME Impossible. (`TO_seq58_progcall_port-20261030T170049Z_m0172_t001`)
  - Check all state-gas-ported numeric/export cond clauses for witness. -> All arithmetic and delegate/coverage/stipend clauses check, but non-precompile clause fails. EVAL-checked refund_probe_destination_is_precompile proves fIN 256w precompile_addresses. No exported falsehood claimed. (`TO_seq58_progcall_port-20261030T170049Z_m0178_t001`, `TO_seq58_progcall_port-20261030T170049Z_m0184_t001`)
- `E0008` (progressed, other, actual effort: 1 sessions, 1 msgs, 14 steps, 13 tools, 5 holbuild, 1,428,377 tok (1,424,358 in, 4,019 out, 1,405,440 cached), 483.9s, $0.2185700)
  - Separate 100w witness, nonprecompile check first, then wf and bounded CALL computation. -> refund_candidate_not_precompile, refund_candidate_impossible and refund_candidate_wf build clean. (`TO_seq58_progcall_port-20261030T170049Z_m0193_t001`)
  - Step dispatch via get_current_context observation instead of unfolding full state; guarded FUNPOW and all concrete rule cond clauses. -> refund_candidate_step, refund_candidate_next_iterates and refund_candidate_rule_conditions checked. StateCost coverage, exact14300 gas cost, stipend2300 and nonprecompile premise all pass. (`TO_seq58_progcall_port-20261030T170049Z_m0201_t001`)
  - Exclude normal final state at PC1, including zero-step case. -> refund_candidate_no_normal_successor_pc proved. Remaining work is full separation observation precondition and SPEC-model bridge, not computational execution. (`TO_seq58_progcall_port-20261030T170049Z_m0203_t001`)
- `E0009` (proved, , actual effort: 1 sessions, 3 msgs, 43 steps, 42 tools, 11 holbuild, 2,986,655 tok (2,981,254 in, 5,401 out, 2,917,120 cached), 1017.3s, $0.4739900)
  - Construct explicit evm domain owning all state-gas-ported CALL pre resources and singleton CALL code; combine with checked concrete cond clauses. -> refund_candidate_pre_holds checks resource/code ownership including originalAccounts and four meters; refund_candidate_rule_conditions checks full numeric/delegate/nonprecompile/coverage clauses and stipend bound. (`TO_seq58_progcall_port-20261030T170049Z_m0241_t001`, `TO_seq58_progcall_port-20261030T170049Z_m0255_t001`)
  - Bridge SPEC_CODE and EVM_SPEC_SEMANTICS to guarded FUNPOW; exclude normal PC1 return including existentially hidden resources. -> refund_candidate_spec_obstruction and refund_candidate_existential_spec_obstruction proved: no SPEC with this admissible pre and normal PC1 post, regardless of arbitrary remaining post resources. Thus both frozen postconditions are obstructed independently of meter port details. (`TO_seq58_progcall_port-20261030T170049Z_m0251_t001`, `TO_seq58_progcall_port-20261030T170049Z_m0255_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261030T170049Z_m0255_t001` (use `read_tool_output` for exact output)

## C1.3

### Current Status

- result: `stuck`
- diagnosis: `wrong_statement`
- latest episode: `E0011`
- blocker: Existing call_exn_safe_step_call asserts unconditional nonempty-context safety, already refuted by historical checked refund witness. Owner-authorized export guards do not repair this universally quantified local helper or its step_inner/run_call consumers.
- actual effort: 1 sessions, 3 steps, 2 tools, 321,059 tok (320,497 in, 562 out, 312,832 cached), 24.3s, $0.0522332
- next: Shallow replan C1.3 safety and finite-return infrastructure with internal meter invariant scoped to reachable callee states; never propagate generic spill<=g as unauthorized export premise. Address consumer stack/global-frame invariants explicitly.

### Attempts / Evidence

- `E0011` (stuck, wrong_statement, actual effort: 1 sessions, 3 steps, 2 tools, 321,059 tok (320,497 in, 562 out, 312,832 cached), 24.3s, $0.0522332)
  - Inspect next failed theorem and forward safety consumers before touching tactics; compare to checked counterexample and existing decreases-gas invariant hypotheses. -> Current source1293-1358 asserts call_exn_safe of step_call/step_inst with only nonempty contexts; step_inner_not_impossible_unimplemented1371 also only assumes nonempty. Historical refund_probe_nonempty_safety_false directly contradicts first statement. DecreasesGas provides spill<=gasUsed hypothesis but no ready nonempty-only replacement. No proof edits made for C1.3; this needs scoped-invariant strategy, not missing consume_gas simp. (`TO_seq58_progcall_port-20261030T183500Z_m0290_t001`, `TO_seq58_progcall_port-20261030T183500Z_m0291_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261030T183500Z_m0290_t001` (use `read_tool_output` for exact output)
- `TO_seq58_progcall_port-20261030T170049Z_m0255_t001` (use `read_tool_output` for exact output)

## C1.3.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0012`
- blocker: 
- actual effort: 2 sessions, 2 msgs, 25 steps, 23 tools, 9 holbuild, 3,093,657 tok (3,089,202 in, 4,455 out, 2,927,744 cached), 321.7s, $0.6602404
- next: Review and commit probe. Proceed C1.3.2 nested prefix boundaries; individual frame backing is checked but not yet established adequate for child gas refunds or for internal frame push/pop.

### Attempts / Evidence

- `E0012` (proved, , actual effort: 2 sessions, 2 msgs, 25 steps, 23 tools, 9 holbuild, 3,093,657 tok (3,089,202 in, 4,455 out, 2,927,744 cached), 321.7s, $0.6602404)
  - Introduce callee-local call_meter_backed c := sp+committed<=gasUsed in standalone probe; prove fresh initialization and preservation by actual meter operations. -> call_meter_initial, charge, credit, commit, restore and restore_to_entry all proved with finite definition and arithmetic proofs. No assumption on suspended caller introduced. (`TO_seq58_progcall_port-20261031T121902Z_m0306_t001`, `TO_seq58_progcall_port-20261031T122504Z_m0321_t001`)
  - Check stipend margin through successful execution charge, creation charge (including spill), then creation credit; audit primitive refund and CREATE abort separately. -> Arithmetic margin and call_meter_charge_credit_stipend prove stipend survives refund from a backed callee, even when charge spills. call_meter_credit_pair has no backing premise and shows primitive credit always normal on nonempty contexts. abort_create equation confirms no grant unuse and no incoming meter hypothesis for that primitive. Main vfmProgCallScript untouched. (`TO_seq58_progcall_port-20261031T121902Z_m0314_t001`, `TO_seq58_progcall_port-20261031T122504Z_m0321_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T122504Z_m0321_t001` (use `read_tool_output` for exact output)

## C1.3.10

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0050`
- blocker: 
- actual effort: 1 sessions, 4 msgs, 60 steps, 59 tools, 15 holbuild, 5,207,785 tok (5,195,158 in, 12,627 out, 5,087,872 cached), 3895.8s, $0.8496292
- next: Review C1.3.10; commit stable return theory. C1.3.11 must integrate isolated return interfaces and layer stipend observations without leaving duplicate old unrestricted safety machinery.

### Attempts / Evidence

- `E0050` (proved, , actual effort: 1 sessions, 4 msgs, 60 steps, 59 tools, 15 holbuild, 5,207,785 tok (5,195,158 in, 12,627 out, 5,087,872 cached), 3895.8s, $0.8496292)
  - Define semantic call_return_gas/data/context; reuse call_meter_settle; prove exact handle_exception memory equation and rooted post-restoration refund bounds. -> Checked all handler branches including REVERT spill restoration, exceptional forfeit, creation-credit cancellation, success absorb/repay. No external caller backing is assumed. (`TO_seq58_progcall_port-20261031T152132Z_m1544_t001`)
  - Relocate structural reachability/last-pop/guarded-trace machinery into isolated vfmCallReturnTheory; derive call_memory_final_pop and run_call_memory_returns with rooted budget and ceiling <= caller.gasUsed. -> Finite ordinary memory-return interface builds with exact returned context and actual refund <= ceiling. Stipend footprint layering and deletion/replacement of old duplicated local chain remain C1.3.11 integration work. General reachability budget needs 2<=n and n<=initial depth; both follow at root entry. (`TO_seq58_progcall_port-20261031T152132Z_m1537_t001`, `TO_seq58_progcall_port-20261031T152132Z_m1544_t001`)
  - Add observation and scalar meter projection theorems for call_return_context. -> Baseline, committed, reservoir, spill, gasUsed, memory/control/log/refund projections checked by boundary simplification; consumers need not unfold merged semantic records. (`TO_seq58_progcall_port-20261031T152132Z_m1544_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T152132Z_m1544_t001` (use `read_tool_output` for exact output)

## C1.3.11

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0054`
- blocker: 
- actual effort: 2 sessions, 1 msgs, 25 steps, 24 tools, 7 holbuild, 2,792,043 tok (2,787,493 in, 4,550 out, 2,619,392 cached), 577.8s, $0.6436412
- next: Review C1.3.11; proceed to C1.4 entry normalization and exact context consumer integration. Consider clean auxiliary target only if necessary, rather than claiming full target success.

### Attempts / Evidence

- `E0051` (progressed, other, actual effort: 1 sessions, 2 msgs, 23 steps, 22 tools, 3 holbuild, 3,007,363 tok (3,004,930 in, 2,433 out, 2,864,896 cached), 661.7s, $0.5908876)
  - Import vfmCallReturnTheory and remove duplicated structural metadata, guarded-trace, old final-pop and unrestricted exception-safety chain from vfmProgCallScript.sml; retarget structural consumers to checked call_return_* facts. -> Build now passes former broken call_exn_safe_step_call prefix and reaches stipend proceed_call. Source shrank from 2826 to about 1305 lines; later stipend/summary consumers are not yet ported. (`TO_seq58_progcall_port-20261031T152132Z_m1552_t001`, `TO_seq58_progcall_port-20261031T152132Z_m1567_t001`)
  - Port call_stipend_prefix_proceed_zero peel with get_accounts/drain_state_gas_reservoir/set_current_context. -> Verified prefix exposes child over drained parent. Old push lemma cannot match because parent has stateGasLeft zeroed. Latest edit replaces that application with direct stipend-prefix list calculation; not built yet when handoff triggered. (`TO_seq58_progcall_port-20261031T152132Z_m1570_t001`, `TO_seq58_progcall_port-20261031T152132Z_m1571_t001`)
- `E0052` (progressed, other, actual effort: 1 sessions, 10 steps, 9 tools, 3 holbuild, 557,113 tok (556,288 in, 825 out, 536,448 cached), 305.0s, $0.1015748)
  - Correct drained-parent direct stipend-prefix normalization to use actual tail t and normalize both subtraction lengths. -> call_stipend_prefix_proceed_zero now checked; build advances through call_stipend_prefix_call_charge to call_stipend_prefix_call. (`TO_seq58_progcall_port-20261031T152132Z_m1584_t001`)
- `E0053` (progressed, other, actual effort: 1 sessions, 2 msgs, 30 steps, 29 tools, 8 holbuild, 2,372,371 tok (2,368,415 in, 3,956 out, 2,317,056 cached), 326.6s, $0.3739836)
  - Replace obsolete combined CALL charge helper by upfront successful consume cutoff; add zero-value get_gas_left/call_gas continuation bound. -> Checked call_stipend_prefix_call and all opcode/step_inner stipend preservation. (`TO_seq58_progcall_port-20261031T152132Z_m1602_t001`)
  - Add successful handle_exception_memory_observation boundary; restrict local step/handler stipend preservation to INL trace steps and consume observation rather than invalid old refund premise. -> Checked run_call_stipend_originalAccounts, handle_step_noncode_rollback and Finalise run_call_stipend_footprint. Build reaches stale call_returns_summary entered branch. (`TO_seq58_progcall_port-20261031T152132Z_m1616_t001`)
- `E0054` (proved, , actual effort: 2 sessions, 1 msgs, 25 steps, 24 tools, 7 holbuild, 2,792,043 tok (2,787,493 in, 4,550 out, 2,619,392 cached), 577.8s, $0.6436412)
  - Prove stipend CALL cutoff for upfront consume, zero-value call_gas bound, and drained-parent proceed preservation. -> CALL/step/reachability stipend observations checked without extra callee or external caller conditions. (`TO_seq58_progcall_port-20261031T152132Z_m1602_t001`)
  - Use successful handler metadata observation and restrict stipend trace steps to INL; assemble exact conditional credited-abort / call_return_context summary with singleton root budget. -> call_abort_context_pair, run_call_stipend_footprint and Finalise call_returns_summary all checked. Align independent return errors via call_memory_final_pop and final stack success word equality. Main build now fails in downstream C1.4 call_entry_prepared[normalize_entry], not C1.3.11. Full target is NOT yet build-clean. (`TO_seq58_progcall_port-20261031T152132Z_m1644_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T152132Z_m1644_t001` (use `read_tool_output` for exact output)

## C1.3.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0013`
- blocker: 
- actual effort: 2 sessions, 1 msgs, 20 steps, 19 tools, 5 holbuild, 1,209,637 tok (1,205,401 in, 4,236 out, 1,108,992 cached), 203.3s, $0.3460772
- next: Review bounded nested-frame probes and commit. Then C1.3.3 finite-run strategy checkpoint before authorizing full invariant/finite-return machinery. Remaining integration must prove margin before push (including stipend), ancestor-budget preservation, and exceptional-return restore/forfeit branches.

### Attempts / Evidence

- `E0013` (proved, , actual effort: 2 sessions, 1 msgs, 20 steps, 19 tools, 5 holbuild, 1,209,637 tok (1,205,401 in, 4,236 out, 1,108,992 cached), 203.3s, $0.3460772)
  - Check exact pop boundary and concrete two-frame per-frame-backing counterexample, with parent gasUsed=spill=10 and child unused grant=10. -> Checked counterexample shows both frames individually backed yet a successful actual pop leaves parent unbacked. Exact pop boundary carries only gasLeft<=caller.gasUsed, no backing premise on external caller. (`TO_seq58_progcall_port-20261031T122624Z_m0346_t001`)
  - Prove strengthened adjacent-frame margin through success absorb/repay and failure credit, restore refund equation, and actual proceed_call/proceed_create push observations. -> All checked. Required suspended-parent margin is own spill+committed + child unused gas+spill+committed <= parent.gasUsed. Restore of backed child with gasUsed<=gasLimit enlarges unused gas by exactly spill+committed. Fresh child and drained-parent push equations preserve this margin when incoming parent has own backing plus grant covered. Root initialization remains independent of arbitrary external caller. These are bounded interfaces, not opcode-wide or entire-prefix preservation. (`TO_seq58_progcall_port-20261031T123059Z_m0352_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T122624Z_m0346_t001` (use `read_tool_output` for exact output)
- `TO_seq58_progcall_port-20261031T123059Z_m0352_t001` (use `read_tool_output` for exact output)

## C1.3.3

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0014`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 27 steps, 26 tools, 3 holbuild, 2,474,768 tok (2,467,807 in, 6,961 out, 2,420,608 cached), 322.4s, $0.4060688
- next: Mandatory scoped PLAN update before accepting parent complete or beginning C1.4: evaluate proposed budget and add executable preservation, safety, collection-return, final-pop/summary and stipend leaves. Commit checked audit/probe changes after review.

### Attempts / Evidence

- `E0014` (proved, , actual effort: 1 sessions, 1 msgs, 27 steps, 26 tools, 3 holbuild, 2,474,768 tok (2,467,807 in, 6,961 out, 2,420,608 cached), 322.4s, $0.4060688)
  - Audit exact finite-run consumer signatures, unrestricted safety chain, existing wf/gas_stack invariants and final-pop/summary statements. -> Recorded source-location and premise/provider map in prog/AUDIT_seq58_call_safety.md. Total run_call_eq_tr and trace extraction are unconditional and reusable; INL collection return depends on false unrestricted step_inner safety. Existing gas_stack_ok omits own backing and committed descendants. Production final-pop and summary still have old meter-free conclusions and need restatement. (`TO_seq58_progcall_port-20261031T123059Z_m0364_t001`, `TO_seq58_progcall_port-20261031T123059Z_m0365_t001`, `TO_seq58_progcall_port-20261031T123059Z_m0367_t001`, `TO_seq58_progcall_port-20261031T123059Z_m0368_t001`)
  - Test refundable claim including committed balance, actual restore/forfeit, paid stipend push budget, success-pop ancestor currency and creation refund credit. -> Clean probe build. Fresh root claim equals grant; ordinary restore preserves claim, forfeit reduces it; stipend<=opcode cost supplies both fresh-parent backing and nonincreasing ancestor total; success pop conserves parent+child claim; credit preserves claim on backed frames. Corrected prior comment: full entry restoration erases spill+committed but ordinary REVERT restores spill only. Proposed exact scoped budget and proof outputs in audit, explicitly not yet proved opcode-wide. (`TO_seq58_progcall_port-20261031T123059Z_m0381_t001`, `TO_seq58_progcall_port-20261031T123059Z_m0384_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T123059Z_m0384_t001` (use `read_tool_output` for exact output)
- `TO_seq58_progcall_port-20261031T123059Z_m0385_t001` (use `read_tool_output` for exact output)

## C1.3.4

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0015`
- blocker: 
- actual effort: 1 sessions, 3 msgs, 40 steps, 39 tools, 16 holbuild, 2,481,475 tok (2,474,986 in, 6,489 out, 2,429,952 cached), 374.4s, $0.3979532
- next: Review C1.3.4, commit new budget theory with required trailer, then scheduled semantic primitive contracts C1.3.5.

### Attempts / Evidence

- `E0015` (proved, , actual effort: 1 sessions, 3 msgs, 40 steps, 39 tools, 16 holbuild, 2,481,475 tok (2,474,986 in, 6,489 out, 2,429,952 cached), 374.4s, $0.3979532)
  - Define recursive accumulated descendant chain with total/prefix/budget; prove indexed equivalence and list monotonicity/replacement/push/pop. -> New vfmCallBudgetTheory builds; recursive chain equivalent to specified EL/TAKE/SUM budget. Local scalar premises isolate semantic consumers from list arithmetic. ()
  - Lift list rules to state prefix and test fresh root, active backing, adjacent margin, root claim/refund and root exit. -> All checked without external caller premises. Fresh root initializes at LENGTH rest+2; internal successful absorb/repay settlement exercises list pop using checked scalar probe lemmas. (`TO_seq58_progcall_port-20261031T123059Z_m0441_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T123059Z_m0441_t001` (use `read_tool_output` for exact output)

## C1.3.5

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0016`
- blocker: 
- actual effort: 1 sessions, 3 msgs, 36 steps, 35 tools, 16 holbuild, 3,167,786 tok (3,160,790 in, 6,996 out, 3,116,288 cached), 376.8s, $0.4705928
- next: Review primitive boundary component, commit stable theory, then scheduled fresh CALL/CREATE push/entry proofs.

### Attempts / Evidence

- `E0016` (proved, , actual effort: 1 sessions, 3 msgs, 36 steps, 35 tools, 16 holbuild, 3,167,786 tok (3,160,790 in, 6,996 out, 3,116,288 cached), 376.8s, $0.4705928)
  - Build call_meter_result boundary contracts for consume, charge, credit, account charge/credit, restore, restore-to-entry, commit, drain, forfeit, repay, restore-forfeit. -> All results retain exact context tail, backing and gasUsed<=gasLimit, and nonincrease of claim. Consume/charge cover returned errors, not only INL states. New standalone vfmCallMeterTheory builds. ()
  - Separate grant transfer contracts from nonincrease: exact unuse/restore-child pairs, consume grant margin/claim conservation, withhold grant, return-grant composition, budget lifting. -> Checked grant exchange interfaces permit claim increases only by the recorded returned grant. Composite consumer return_grant uses boundary theorem rather than semantic unfolding. (`TO_seq58_progcall_port-20261031T123059Z_m0483_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T123059Z_m0483_t001` (use `read_tool_output` for exact output)

## C1.3.6

### Current Status

- result: `stuck`
- diagnosis: `missing_helper`
- latest episode: `E0017`
- blocker: Nested entry scalar/list boundaries are checked, but full step_call/step_create and precompile execution need compositional meter/safety interfaces not supplied by preceding components. proceed_call dispatches precompiles immediately after push; its general budget contract therefore requires precompile preservation before step_call, not only later all-opcode work.
- actual effort: 1 sessions, 2 msgs, 23 steps, 22 tools, 5 holbuild, 2,615,372 tok (2,611,287 in, 4,085 out, 2,567,040 cached), 267.5s, $0.3860480
- next: Review scoped missing dependency: preserve entry shape/budget partial work, introduce or assign compositional meter+exception-safety interface and ordinary primitive/precompile laws before whole step_call/step_create, avoiding a flat 1500-line duplicated local safety library.

### Attempts / Evidence

- `E0017` (stuck, missing_helper, actual effort: 1 sessions, 2 msgs, 23 steps, 22 tools, 5 holbuild, 2,615,372 tok (2,611,287 in, 4,085 out, 2,567,040 cached), 267.5s, $0.3860480)
  - Expose exact proceed_create and non-precompile proceed_call push shapes, with zero child gasUsed, child claim=grant and backed child; lift to rooted budget against original pre-grant frame. -> vfmCallEntryTheory clean. Checked shape/budget proofs use scalar grant-margin and total-claim premises. These are meaningful partial C1.3.6 outputs, not step_call preservation. (`TO_seq58_progcall_port-20261031T123059Z_m0508_t001`)
  - Audit whole step_call composition and precompile branch against current interfaces. -> Current production call_exn_safe_step_call relies on local safety-only bind rules and false nonempty precondition (source 1293-1357). Primitive call_meter_result facts preserve meters/tail but do not yet compose through stack/memory/access readers or expose forbidden-error exclusion; precompile contracts also absent. Direct unfolding proceed_call with unresolved condition produced >4KB goal, fixed locally by split; repeating that approach for step_call violates abstraction hygiene. ()

### Evidence refs

- `TO_seq58_progcall_port-20261031T123059Z_m0508_t001` (use `read_tool_output` for exact output)
- `TO_seq58_progcall_port-20261031T123059Z_m0500_t001` (use `read_tool_output` for exact output)
- `TO_seq58_progcall_port-20261031T123059Z_m0493_t001` (use `read_tool_output` for exact output)
- `TO_seq58_progcall_port-20261031T123059Z_m0496_t001` (use `read_tool_output` for exact output)

## C1.3.6.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0018`
- blocker: 
- actual effort: 1 sessions, 2 steps, 1 tools, 1 holbuild, 262,622 tok (262,398 in, 224 out, 258,432 cached), 13.9s, $0.0360152
- next: Review/commit bounded entry facts, then C1.3.6.2 composition probes.

### Attempts / Evidence

- `E0018` (proved, , actual effort: 1 sessions, 2 steps, 1 tools, 1 holbuild, 262,622 tok (262,398 in, 224 out, 258,432 cached), 13.9s, $0.0360152)
  - Audit current five entry boundaries and rebuild vfmCallEntryTheory. -> Shape/budget CALL facts explicitly exclude precompiles; both budget corollaries compare with original frame u before grant, using scalar pair ceiling/margin. No whole-step preservation claimed. Build clean. (`TO_seq58_progcall_port-20261031T123059Z_m0518_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T123059Z_m0518_t001` (use `read_tool_output` for exact output)

## C1.3.6.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0019`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 21 steps, 20 tools, 8 holbuild, 1,218,376 tok (1,216,396 in, 1,980 out, 1,189,504 cached), 169.7s, $0.1925344
- next: Review then commit safe-contract theory; continue scheduled neutral-operation adapters.

### Attempts / Evidence

- `E0019` (proved, , actual effort: 1 sessions, 1 msgs, 21 steps, 20 tools, 8 holbuild, 1,218,376 tok (1,216,396 in, 1,980 out, 1,189,504 cached), 169.7s, $0.1925344)
  - Defined result-indexed safe contract and proved return/fail/consequence/bind/ignore-bind/invariant/from-result laws; explicitly specialize first bind contract before sum splitting. -> All contract laws verified. Both successful and failed intermediate result states retain their postcondition. ()
  - Added consume adapter and composition probes for consume-return, early OutOfGas, and backed restore_child_gas. -> vfmCallMeterSafeTheory builds clean; restoration probe obtains INL and meter result from existing grant premise. (`TO_seq58_progcall_port-20261031T123059Z_m0551_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T123059Z_m0551_t001` (use `read_tool_output` for exact output)

## C1.3.6.3

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0020`
- blocker: 
- actual effort: 1 sessions, 3 msgs, 57 steps, 56 tools, 19 holbuild, 4,811,267 tok (4,803,011 in, 8,256 out, 4,725,888 cached), 495.9s, $0.7093948
- next: Review adapters then commit; next scheduled precompile preservation.

### Attempts / Evidence

- `E0020` (proved, , actual effort: 1 sessions, 3 msgs, 57 steps, 56 tools, 19 holbuild, 4,811,267 tok (4,803,011 in, 8,256 out, 4,725,888 cached), 495.9s, $0.7093948)
  - Introduced call_meter_ready and call_meter_neutral with result lifting; proved generic state/context reader and update boundaries and instantiated stack, memory, address/domain, account, return-data, pc and static-assert operations. -> Neutral preservation allows reservoir and unrelated fields to change, but requires gas limit, used, spill and committed equality. Memory/pc consumers use generic updater; stack checks allow underflow/overflow on all result states. ()
  - Wrapped existing primitive meter result laws with independent forbidden-error checks; covered charge/credit/new-account, drain, restore/restore-entry, commit, forfeit, repay and stronger withhold grant adapter. -> vfmCallMeterOpsTheory builds clean; withhold retains grant-specific result rather than unrestricted meter preservation. (`TO_seq58_progcall_port-20261031T123059Z_m0613_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T123059Z_m0613_t001` (use `read_tool_output` for exact output)

## C1.3.6.4

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0021`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 11 steps, 10 tools, 4 holbuild, 1,453,734 tok (1,452,843 in, 891 out, 1,437,696 cached), 154.3s, $0.1829736
- next: Review and commit precompile boundaries, then scheduled whole entry composition.

### Attempts / Evidence

- `E0021` (proved, , actual effort: 1 sessions, 1 msgs, 11 steps, 10 tools, 4 holbuild, 1,453,734 tok (1,452,843 in, 891 out, 1,437,696 cached), 154.3s, $0.1829736)
  - Lift fixed-tail primitive safe contracts over prior call_meter_result spends; factor read/consume and optional-output precompile skeletons, prove separate safe contracts for all 18 precompiles. -> All cryptographic computations remain opaque; only option/pair/boolean outcomes are split. Composition preserves all failure result states. ()
  - Enumerate finite precompile address set, combine separate contracts under membership and derive raw result and rooted budget corollaries. -> vfmCallPrecompileTheory builds clean. Address-membership premise retained; no unsafe Impossible default admitted. (`TO_seq58_progcall_port-20261031T133309Z_m0655_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T133309Z_m0655_t001` (use `read_tool_output` for exact output)

## C1.3.6.5

### Current Status

- result: `progressed`
- diagnosis: `missing_helper`
- latest episode: `E0023`
- blocker: Whole-entry composition needs a surplus-preserving contract: current safe neutral adapters return call_meter_result, dropping the margin and claim+margin facts needed after opcode payment. This is an interface gap, not a failed scalar inequality.
- actual effort: 2 sessions, 3 msgs, 43 steps, 41 tools, 14 holbuild, 3,033,257 tok (3,027,819 in, 5,438 out, 2,870,784 cached), 498.7s, $0.6555284
- next: Request strategist guidance on surplus-preserving composition before unfolding any whole opcode.

### Attempts / Evidence

- `E0022` (progressed, other, actual effort: 1 sessions, 2 msgs, 27 steps, 26 tools, 11 holbuild, 1,724,261 tok (1,721,739 in, 2,522 out, 1,675,008 cached), 268.4s, $0.2861828)
  - Added general proceed_call all-result budget boundary in isolated EntryStepTheory; split transfer and precompile membership, use entry_budget then dispatch_budget. -> Build clean. Covers immediate dispatch and forbidden errors, no opcode consumer unfolding of crypto. Initial witness and abbreviation normalization issues resolved. (`TO_seq58_progcall_port-20261031T133309Z_m0692_t001`)
- `E0023` (progressed, missing_helper, actual effort: 2 sessions, 3 msgs, 43 steps, 41 tools, 14 holbuild, 3,033,257 tok (3,027,819 in, 5,438 out, 2,870,784 cached), 498.7s, $0.6555284)
  - Proved consume_margin, charge_margin and credit_margin; proved call_gas zero-cost grant arithmetic with stipend explicitly backed by a paid margin. -> EntryStepTheory builds all five new boundary theorems. Account charging/refunding preserve paid surplus over spill+committed. call_gas bounds use zero cost arguments and do not assume old call_gas cost treatment. (`TO_seq58_progcall_port-20261031T134530Z_m0706_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T134530Z_m0706_t001` (use `read_tool_output` for exact output)

## C1.3.6.5.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0024`
- blocker: 
- actual effort: 1 sessions, 3 msgs, 49 steps, 48 tools, 18 holbuild, 5,421,597 tok (5,413,531 in, 8,066 out, 5,352,704 cached), 615.4s, $0.7375844
- next: Review reservation interface and commit; then reservation acquisition/discharge leaf.

### Attempts / Evidence

- `E0024` (proved, , actual effort: 1 sessions, 3 msgs, 49 steps, 48 tools, 18 holbuild, 5,421,597 tok (5,413,531 in, 8,066 out, 5,352,704 cached), 615.4s, $0.7375844)
  - Defined call_meter_reserved with fixed anchor; proved zero/result equivalence, weakening, forget, ready, neutral and margin transport; proved neutral adapters, value-retaining readers, charge/credit account adapters. -> All requested interfaces build clean in ReserveTheory. All-result preservation and forbidden-error exclusion included. Polymorphic context reader specialization requires Q.ISPEC_THEN and beta normalization; primitive margin matching uses explicit arithmetic normalization rather than broad metis. (`TO_seq58_progcall_port-20261031T134530Z_m0761_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T134530Z_m0761_t001` (use `read_tool_output` for exact output)

## C1.3.6.5.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0026`
- blocker: 
- actual effort: 1 sessions, 2 msgs, 31 steps, 30 tools, 8 holbuild, 2,060,753 tok (2,057,622 in, 3,131 out, 2,009,984 cached), 309.7s, $0.3275844

### Attempts / Evidence

- `E0025` (progressed, other, actual effort: 1 sessions, 1 msgs, 15 steps, 14 tools, 4 holbuild, 2,010,740 tok (2,007,541 in, 3,199 out, 1,847,936 cached), 213.5s, $0.5359936)
  - Added GrantTheory with consume-success/all-result acquisition, CREATE withholding, child refund discharge; then CALL payment and proceed wrappers. -> First four theorems built clean in TO_m0775. Last build checked CALL payment but failed proceed_call wrapper because gvs normalized n<=LENGTH u.contexts into n<=SUC LENGTH rest, so drule_all lacked literal premise. Added original length inequality by simp; this last edit is unbuilt. CREATE wrapper likely needs same repair. Abort adapters remain unwritten. (`TO_seq58_progcall_port-20261031T134530Z_m0775_t001`, `TO_seq58_progcall_port-20261031T134530Z_m0777_t001`, `TO_seq58_progcall_port-20261031T134530Z_m0778_t001`)
- `E0026` (proved, , actual effort: 1 sessions, 2 msgs, 31 steps, 30 tools, 8 holbuild, 2,060,753 tok (2,057,622 in, 3,131 out, 2,009,984 cached), 309.7s, $0.3275844)
  - Completed GrantTheory acquisition, grant-payment, entry wrappers and abort adapters using reserved predicate, safe bind and consequence. -> vfmCallGrantTheory builds clean. Unuse discharges surplus directly via checked pair boundary; early push failures forget reservation rather than assert refund. CREATE collision preserves ordinary result without refund. Fixed literal length premises, partial predicate rewrite mismatch, beta reduction and ready/result post mismatch. (`TO_seq58_progcall_port-20261031T140620Z_m0814_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T140620Z_m0814_t001` (use `read_tool_output` for exact output)

## C1.3.6.5.3

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0030`
- blocker: 
- actual effort: 3 sessions, 7 msgs, 97 steps, 94 tools, 32 holbuild, 8,850,274 tok (8,839,131 in, 11,143 out, 8,431,616 cached), 4733.9s, $1.7696216

### Attempts / Evidence

- `E0027` (progressed, other, actual effort: 1 sessions, 3 msgs, 43 steps, 42 tools, 18 holbuild, 4,002,648 tok (3,996,818 in, 5,830 out, 3,938,560 cached), 477.7s, $0.5686720)
  - Built CallStepsTheory with credit+abort contracts, anchor-result-to-budget lifting, reservation/budget bind, depth tail, balance/callee tail and fixed-context grant-payment tail. -> All seven suffix/composition theorems build clean. Whole step_call remains unwritten; next is get_gas_left and variable call_gas bind then charge/static/expand prefix and initial readers/payment. No opcode or precompile internals unfolded. (`TO_seq58_progcall_port-20261031T140620Z_m0858_t001`, `TO_seq58_progcall_port-20261031T140620Z_m0862_t001`)
- `E0028` (progressed, other, actual effort: 2 sessions, 4 msgs, 56 steps, 54 tools, 21 holbuild, 5,410,348 tok (5,403,036 in, 7,312 out, 5,220,352 cached), 827.9s, $0.9605232)
  - Composed get_gas_left success-sensitive reader with call_gas pair split and checked payment_tail. -> call_meter_reserved_gas_tail builds. Reasserted n<=LENGTH u.contexts after gvs before directed boundary application. All CallSteps suffix lemmas are now checked; whole opcode prefix still pending. (`TO_seq58_progcall_port-20261031T142258Z_m0875_t001`)
- `E0029` (progressed, other, actual effort: 2 sessions, 3 msgs, 44 steps, 42 tools, 15 holbuild, 3,303,904 tok (3,299,743 in, 4,161 out, 3,180,032 cached), 2160.6s, $0.5990352)
  - Compose opaque charge/static/memory reservation adapters, consume-success stipend acquisition, and checked gas_tail. -> Three new lemmas build: charge_memory_bind, consume_budget_bind, cost_tail. cost_tail covers all meter-changing CALL entry and abort/proceed suffixes. Initial pop/read/access/delegate prefix remains. (`TO_seq58_progcall_port-20261031T142943Z_m0928_t001`)
- `E0030` (proved, , actual effort: 3 sessions, 7 msgs, 97 steps, 94 tools, 32 holbuild, 8,850,274 tok (8,839,131 in, 11,143 out, 8,431,616 cached), 4733.9s, $1.7696216)
  - Compose reservation-preserving charge/static/memory prefix, stipend-acquiring consume, zero-reservation initial pop/read/access/delegate prefix and checked grant suffix. -> call_meter_reserved_step_call proves all-result whole-opcode safety with opaque primitive interfaces. call_meter_step_call_budget initializes zero reservation from wf_state, positive protected depth and rooted budget; proves budget preservation and excludes Impossible/Unimplemented. (`TO_seq58_progcall_port-20261031T152132Z_m0981_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T152132Z_m0981_t001` (use `read_tool_output` for exact output)

## C1.3.6.5.4

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0032`
- blocker: 
- actual effort: 1 sessions, 3 msgs, 39 steps, 38 tools, 13 holbuild, 2,686,683 tok (2,682,394 in, 4,289 out, 2,622,592 cached), 499.4s, $0.4247532

### Attempts / Evidence

- `E0031` (progressed, other, actual effort: 1 sessions, 2 msgs, 8 steps, 7 tools, 1 holbuild, 1,081,872 tok (1,080,985 in, 887 out, 926,720 cached), 131.3s, $0.4100720)
  - Start CREATE suffix with withhold_create_gas then collision abort_create_exists or proceed_create using reservation interfaces. -> Withholding bind prefix checks. Collision consequence leaves reservation-forgetting implication unsolved by simp; stopped for forced handoff before adding explicit strip/metis. Whole CREATE not yet composed; uncommitted suffix theorem is currently failing. (`TO_seq58_progcall_port-20261031T152132Z_m0993_t001`)
- `E0032` (proved, , actual effort: 1 sessions, 3 msgs, 39 steps, 38 tools, 13 holbuild, 2,686,683 tok (2,682,394 in, 4,289 out, 2,622,592 cached), 499.4s, $0.4247532)
  - Compose CREATE grant, charge, depth/abort and check suffixes with reservation-safe bind; assemble whole step_create and lift fresh zero reservation to rooted budget. -> call_meter_reserved_step_create and call_meter_step_create_budget build cleanly. Collision forgets reservation without refund; early abort uses ordinary result. Whole assembly uses checked interfaces and DISJ_ASSOC to normalize the two early-abort conditions. (`TO_seq58_progcall_port-20261031T152132Z_m1037_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T152132Z_m1037_t001` (use `read_tool_output` for exact output)

## C1.3.7

### Current Status

- result: `progressed`
- diagnosis: `other`
- latest episode: `E0033`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 21 steps, 20 tools, 2 holbuild, 2,013,390 tok (2,010,941 in, 2,449 out, 1,972,096 cached), 175.9s, $0.2993896
- next: Continue finite opcode coverage with memory/storage/terminal families, then dispatch and step_inner lift. New vfmCallInnerScript.sml is build-clean and untracked until stable checkpoint commit.

### Attempts / Evidence

- `E0033` (progressed, other, actual effort: 1 sessions, 1 msgs, 21 steps, 20 tools, 2 holbuild, 2,013,390 tok (2,010,941 in, 2,449 out, 1,972,096 cached), 175.9s, $0.2993896)
  - Start downstream vfmCallInner theory and compose ordinary-result invariant adapters for pop, arithmetic and context/transaction-reader opcode families. -> Ten interface-based helper theorems build cleanly, covering binop, monop, modop, exp, context/msgParams/txParams families. No whole opcode dispatch theorem yet. (`TO_seq58_progcall_port-20261031T152132Z_m1063_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T152132Z_m1063_t001` (use `read_tool_output` for exact output)

## C1.3.7.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0034`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 20 steps, 19 tools, 9 holbuild, 2,437,417 tok (2,433,383 in, 4,034 out, 2,406,272 cached), 268.2s, $0.3351892

### Attempts / Evidence

- `E0034` (proved, , actual effort: 1 sessions, 1 msgs, 20 steps, 19 tools, 9 holbuild, 2,437,417 tok (2,433,383 in, 4,034 out, 2,406,272 cached), 268.2s, $0.3351892)
  - Introduce value-sensitive current reader and saved-context continuation boundary; compose stack/control-flow consumers using neutral set, ready assertion prefix, and ordinary-result invariant adapters. -> Pop, Push, Dup, DupN, Swap, SwapN, Exchange, Jump, JumpI, and inc_pc_or_jump all proved with all-result meter/safety contracts. Saved-context operations require exact current-frame provenance; neutral field updates preserve all four claim dimensions and gasLimit. vfmCallInnerTheory builds cleanly. (`TO_seq58_progcall_port-20261031T152132Z_m1091_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T152132Z_m1091_t001` (use `read_tool_output` for exact output)

## C1.3.7.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0036`
- blocker: 
- actual effort: 1 sessions, 2 msgs, 24 steps, 23 tools, 7 holbuild, 1,565,171 tok (1,561,227 in, 3,944 out, 1,517,696 cached), 222.8s, $0.2782716
- next: Review and commit read/memory/copy/log family; proceed to scheduled storage family.

### Attempts / Evidence

- `E0035` (progressed, other, actual effort: 1 sessions, 1 msgs, 10 steps, 9 tools, 1 holbuild, 1,359,877 tok (1,358,192 in, 1,685 out, 1,244,416 cached), 86.9s, $0.3688436)
  - Add account/callee/access invariant adapters, source readers and generalized copy_source/copy_memory composition. -> Account/callee adapters pass; access_inv currently fails because ready-to-ready access_address contract is not directly a ready-to-result contract. Need explicit conversion with call_meter_ready_result before result_lift. Source-reader and copy helpers after that point remain unchecked, not proved. (`TO_seq58_progcall_port-20261031T152132Z_m1103_t001`, `TO_seq58_progcall_port-20261031T152132Z_m1106_t001`)
- `E0036` (proved, , actual effort: 1 sessions, 2 msgs, 24 steps, 23 tools, 7 holbuild, 1,565,171 tok (1,561,227 in, 3,944 out, 1,517,696 cached), 222.8s, $0.2782716)
  - Convert ready-preserving access boundary to result; verify source reader and generalized copy helpers. -> Access adapter and entire copy_source/copy_memory suffix build. (`TO_seq58_progcall_port-20261031T152132Z_m1114_t001`)
  - Compose ordinary balance, code size/hash, data load/copy, block/blob hash, self balance and log contracts from fixed-tail interfaces. -> All family helpers and explicit CallDataCopy/CodeCopy/MCopy instances build; environmental operations remain covered by existing generic context/msgParams/txParams contracts. (`TO_seq58_progcall_port-20261031T152132Z_m1130_t001`, `TO_seq58_progcall_port-20261031T152132Z_m1133_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T152132Z_m1114_t001` (use `read_tool_output` for exact output)
- `TO_seq58_progcall_port-20261031T152132Z_m1133_t001` (use `read_tool_output` for exact output)

## C1.3.7.3

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0037`
- blocker: 
- actual effort: 1 sessions, 2 msgs, 21 steps, 20 tools, 6 holbuild, 1,793,496 tok (1,790,183 in, 3,313 out, 1,760,768 cached), 196.2s, $0.2680368
- next: Review and commit storage safety family, then scheduled terminal opcode family.

### Attempts / Evidence

- `E0037` (proved, , actual effort: 1 sessions, 2 msgs, 21 steps, 20 tools, 6 holbuild, 1,793,496 tok (1,790,183 in, 3,313 out, 1,760,768 cached), 196.2s, $0.2680368)
  - Lift state charge/refund and build storage-specific neutral access/read/write/refund adapters. -> Primitive adapters build; slot access covers domain failures and preserves fixed contexts. Context refund update requires higher-order matching. (`TO_seq58_progcall_port-20261031T152132Z_m1153_t001`)
  - Compose sload, separate sstore gas tail, whole sstore gas consumption, and transient/nontransient sstore. -> All storage family contracts build with no added caller conditions, including exceptional charge results. (`TO_seq58_progcall_port-20261031T152132Z_m1159_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T152132Z_m1159_t001` (use `read_tool_output` for exact output)

## C1.3.7.4

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0038`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 8 steps, 7 tools, 1 holbuild, 778,351 tok (776,448 in, 1,903 out, 763,648 cached), 71.9s, $0.1209948
- next: Review and commit terminal family; assemble ordinary dispatch and inner execution as scheduled.

### Attempts / Evidence

- `E0038` (proved, , actual effort: 1 sessions, 1 msgs, 8 steps, 7 tools, 1 holbuild, 778,351 tok (776,448 in, 1,903 out, 763,648 cached), 71.9s, $0.1209948)
  - Prove terminal, return-data, deletion and account-charge adapters; compose Return/Revert and selfdestruct through isolated neutral tail. -> All terminal family theorems build on first attempt, covering both return flags and all selfdestruct charge/access failure paths. No popping claimed at instruction level. (`TO_seq58_progcall_port-20261031T152132Z_m1172_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T152132Z_m1172_t001` (use `read_tool_output` for exact output)

## C1.3.7.5

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0039`
- blocker: 
- actual effort: 1 sessions, 2 msgs, 27 steps, 26 tools, 8 holbuild, 3,041,088 tok (3,038,005 in, 3,083 out, 3,000,192 cached), 326.8s, $0.4064752
- next: Review and commit dispatch and inner execution; proceed to handler/finite return components.

### Attempts / Evidence

- `E0039` (proved, , actual effort: 1 sessions, 2 msgs, 27 steps, 26 tools, 8 holbuild, 3,041,088 tok (3,038,005 in, 3,083 out, 3,000,192 cached), 326.8s, $0.4064752)
  - Finite ordinary dispatch; lift fixed-tail contracts to anchored budget, combine CALL/CREATE contracts, and compose PC handling and fetch. -> All ordinary constructors checked; whole step_inst and step_inner budget preservation plus forbidden-exception exclusion build. CALL PC is noop; ordinary PC remains fixed-tail, avoiding any post-CALL fixed-tail assumption. (`TO_seq58_progcall_port-20261031T152132Z_m1185_t001`, `TO_seq58_progcall_port-20261031T152132Z_m1204_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T152132Z_m1204_t001` (use `read_tool_output` for exact output)

## C1.3.8

### Current Status

- result: `stuck`
- diagnosis: `risk_mismatch`
- latest episode: `E0041`
- blocker: Exact pop equation produces a large settled context expression; simplification of its abbreviation with scalar meter definitions times out. Need a compact settlement interface before semantic pop consumer.
- actual effort: 1 sessions, 1 msgs, 19 steps, 18 tools, 5 holbuild, 1,156,213 tok (1,154,162 in, 2,051 out, 1,119,616 cached), 386.0s, $0.2015636
- next: Review handler decomposition: expose settled-context backing and claim contracts without expanding full context records inside semantic consumer.

### Attempts / Evidence

- `E0040` (progressed, other, actual effort: 1 sessions, 1 msgs, 12 steps, 11 tools, 1 holbuild, 1,534,028 tok (1,532,084 in, 1,944 out, 1,508,736 cached), 121.7s, $0.2170096)
  - Prove reraise/output reader interfaces and isolate code-deposit execution/state charge sequence; compose handle_create. -> call_meter_safe_handle_create_inv builds for every result under only e not forbidden, preserving fixed-tail call_meter_result. No handler-pop proof yet. (`TO_seq58_progcall_port-20261031T152132Z_m1219_t001`)
- `E0041` (stuck, risk_mismatch, actual effort: 1 sessions, 1 msgs, 19 steps, 18 tools, 5 holbuild, 1,156,213 tok (1,154,162 in, 2,051 out, 1,119,616 cached), 386.0s, $0.2015636)
  - Use parent_margin, exact call_meter_pop_pair and call_meter_budget_pop, then simplify both settlement branches. -> List matching succeeded with goal_assum/drule_at, but scalar settled obligation carries large repeated merged expressions. simp Abbr and gvs Abbr plus scalar definitions both exceed 30 seconds. Reverted experimental theorem; existing code-deposit proof retained. (`TO_seq58_progcall_port-20261031T152132Z_m1247_t001`, `TO_seq58_progcall_port-20261031T152132Z_m1249_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T152132Z_m1247_t001` (use `read_tool_output` for exact output)
- `TO_seq58_progcall_port-20261031T152132Z_m1249_t001` (use `read_tool_output` for exact output)

## C1.3.8.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0042`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 8 steps, 7 tools, 3 holbuild, 616,509 tok (614,432 in, 2,077 out, 601,600 cached), 123.3s, $0.1065940

### Attempts / Evidence

- `E0042` (proved, , actual effort: 1 sessions, 1 msgs, 8 steps, 7 tools, 3 holbuild, 616,509 tok (614,432 in, 2,077 out, 601,600 cached), 123.3s, $0.1065940)
  - Define call_meter_settle on arbitrary merged context; prove generic backing/claim, absorption backing/usage/claim, and compose pop corollaries. -> All scalar interfaces build; compact call_meter_pop_settle_pair identifies exact semantic expression by pure rewriting without expanding semantic records. (`TO_seq58_progcall_port-20261031T152132Z_m1260_t001`, `TO_seq58_progcall_port-20261031T152132Z_m1262_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T152132Z_m1260_t001` (use `read_tool_output` for exact output)
- `TO_seq58_progcall_port-20261031T152132Z_m1262_t001` (use `read_tool_output` for exact output)

## C1.3.8.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0048`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 21 steps, 20 tools, 4 holbuild, 2,350,677 tok (2,348,423 in, 2,254 out, 2,320,384 cached), 1034.2s, $0.3106564
- next: Ancestor review should schedule remaining nonabort/finite-return interface using authorized caller grant bound, not unconditional root safety.

### Attempts / Evidence

- `E0043` (progressed, other, actual effort: 1 sessions, 1 msgs, 11 steps, 10 tools, 3 holbuild, 942,777 tok (941,412 in, 1,365 out, 926,848 cached), 268.8s, $0.1354628)
  - Compose compact pop_settle_pair with parent_margin, budget_pop and settlement corollaries; use root_exit for final pop; lift checked handle_create fixed-tail contract. -> Internal pop ordinary-result/budget, root pop ordinary-result/budget and handle_create all-result budget plus forbidden-exception exclusion build cleanly. New compact settlement eliminates earlier timeout. (`TO_seq58_progcall_port-20261031T152132Z_m1270_t001`, `TO_seq58_progcall_port-20261031T152132Z_m1272_t001`, `TO_seq58_progcall_port-20261031T152132Z_m1278_t001`)
- `E0044` (progressed, other, actual effort: 1 sessions, 1 msgs, 21 steps, 20 tools, 6 holbuild, 1,847,045 tok (1,844,788 in, 2,257 out, 1,822,208 cached), 339.9s, $0.2499508)
  - Lift restore and forfeit fixed-tail contracts, then compose the initial exception-handler restore/forfeit/clear-data prefix. -> call_meter_safe_exception_prepare_inv builds; branches split before unfolding call_meter_safe_def to preserve contract rewrites. Full exception handler and post-pop output remain unfinished. (`TO_seq58_progcall_port-20261031T152132Z_m1288_t001`)
- `E0045` (progressed, other, actual effort: 1 sessions, 5 msgs, 74 steps, 73 tools, 26 holbuild, 7,421,062 tok (7,411,169 in, 9,893 out, 7,319,936 cached), 1339.5s, $1.0133896)
  - Prove observation-only top replacement across active and exited budgets; lift inc_pc, returnData, write_memory and push_stack to budget/nonempty safe contracts, compose actual post-pop output spine. -> call_meter_safe_exception_output builds for both Code and Memory, every result, without backing on external caller. Generic functional-update matching needed explicit witnesses for budget adapters; final safe wrappers use the checked budget boundaries and monad leaf equations. Output composition requires ho_match_mp_tac for expanded predicate lambdas; Memory is first outputTo constructor. (`TO_seq58_progcall_port-20261031T152132Z_m1309_t001`, `TO_seq58_progcall_port-20261031T152132Z_m1334_t001`, `TO_seq58_progcall_port-20261031T152132Z_m1340_t001`)
- `E0046` (progressed, other, actual effort: 1 sessions, 4 msgs, 54 steps, 53 tools, 12 holbuild, 3,968,834 tok (3,963,051 in, 5,783 out, 3,883,776 cached), 6087.2s, $0.6047576)
  - Split root pop on refundable gas <= parent.gasUsed; unsuccessful unuse_gas occurs after shortening contexts. Compose all-result pop budget/nonempty with output safe contract through handle_ex_helper, then fixed-tail prepare into handle_exception. -> call_meter_pop_root_budget_all, call_meter_pop_budget_all, call_meter_exception_tail_budget and call_meter_handle_exception_budget build cleanly. Full handle_step/step and forbidden-exception exclusion remain. No external caller backing assumption was introduced. Generic safe-def metis timed out; selecting the safe assumption and specializing at live result solved it immediately. (`TO_seq58_progcall_port-20261031T152132Z_m1400_t001`)
- `E0047` (progressed, other, actual effort: 1 sessions, 5 msgs, 75 steps, 74 tools, 17 holbuild, 5,943,362 tok (5,935,217 in, 8,145 out, 5,833,088 cached), 6953.7s, $0.8690168)
  - Compose handle_create's all-result budget, wf and length contracts with the checked handle_exception budget theorem. -> call_meter_handle_step_budget proved and target builds. handle_create is result-polymorphic: Cases_on without explicit unit execution_result introduced a distinct type instance whose equation could not rewrite the live handler case; explicit unit annotation fixes it. (`TO_seq58_progcall_port-20261031T152132Z_m1420_t001`)
- `E0048` (proved, , actual effort: 1 sessions, 1 msgs, 21 steps, 20 tools, 4 holbuild, 2,350,677 tok (2,348,423 in, 2,254 out, 2,320,384 cached), 1034.2s, $0.3106564)
  - Strengthen handler budget boundaries in place from wf_state to EVERY (wf_context o FST), extract step_inner_contexts_wf from decreases_gas_cred_step_inner, compose step_inner budget/nonforbidden and nonshrinking stack with handler budget. -> All revised required outputs proved: context-wf handler budget boundaries, step_inner_contexts_wf, call_meter_step_budget. vfmCallInnerTheory builds. Existing lemma names retained; stronger handler input interfaces replace full-wf synthesis. Root forbidden-exception exclusion intentionally not claimed: root unuse_gas may fail after pop and budget then exits; later finite-return safety must supply authorized caller grant bound. (`TO_seq58_progcall_port-20261031T152132Z_m1438_t001`, `TO_seq58_progcall_port-20261031T152132Z_m1450_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T152132Z_m1450_t001` (use `read_tool_output` for exact output)

## C1.3.9

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0049`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 17 steps, 16 tools, 3 holbuild, 2,157,141 tok (2,153,696 in, 3,445 out, 2,126,592 cached), 609.7s, $0.3013172
- next: Review whether finite-return boundary suffices to close this leaf and schedule replacement/removal of old unrestricted local chain when integrating call_returns_summary.

### Attempts / Evidence

- `E0049` (proved, , actual effort: 1 sessions, 1 msgs, 17 steps, 16 tools, 3 holbuild, 2,157,141 tok (2,153,696 in, 3,445 out, 2,126,592 cached), 609.7s, $0.3013172)
  - Place finite-return boundary in prog/vfmCallReturnScript.sml over checked vfmCallInnerTheory; combine scoped inner nonforbidden with existing handler-state and handle_step_not_abort_returns_inl facts; propagate budget/wf/Collect/ISL by OWHILE_INV_IND and apply unconditional run_call_eq_tr. -> call_meter_step_collect_inl, call_meter_run_call_collect_inl, call_meter_run_call_collect_returns build without cheats. Existing spec gas_stack_ok/stack_room preservation plus handle_step_not_abort_returns_inl discharge handler safety including root pop. No extra caller backing was added. New theory isolates valid scoped infrastructure from the old unrestricted safety chain still awaiting consumer integration in vfmProgCallScript.sml; run_call_last_pop left untouched. (`TO_seq58_progcall_port-20261031T152132Z_m1470_t001`, `TO_seq58_progcall_port-20261031T152132Z_m1472_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T152132Z_m1472_t001` (use `read_tool_output` for exact output)

## C1.4

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0056`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 16 steps, 15 tools, 7 holbuild, 1,555,067 tok (1,553,370 in, 1,697 out, 1,522,816 cached), 212.1s, $0.2303596
- next: Review bounded proof and authorize checkpoint commit despite downstream caller_observation_frame failure; proceed to shared frame/export component.

### Attempts / Evidence

- `E0055` (stuck, risk_mismatch, actual effort: 1 sessions, 3 msgs, 35 steps, 34 tools, 11 holbuild, 2,470,622 tok (2,466,347 in, 4,275 out, 2,397,440 cached), 485.2s, $0.4203080)
  - Restated prepared entry to upfront execution charge, reservoir cover, charge triplet, authorized credit bound, and conditional call_abort_context/call_return_context output. -> Statement checks; original obsolete new_account_cost removed from this local theorem. compose_entry not ported yet. (`TO_seq58_progcall_port-20261031T211644Z_m1675_t001`)
  - Peel delegate resolution, consume upfront, normalize charged reservoir using charge_state_gas definitions, then simplify call_gas and remaining consume. -> Advanced past charge to remaining conditional continuations; six expanded goals remain. gvs eliminates aliases and leaves branch splits referring to stale free value, so current tactic is brittle. AC simplification timed out and was removed; small adjacent-sum equality is fast. (`TO_seq58_progcall_port-20261031T211644Z_m1684_t001`, `TO_seq58_progcall_port-20261031T211644Z_m1697_t001`)
- `E0056` (proved, , actual effort: 1 sessions, 1 msgs, 16 steps, 15 tools, 7 holbuild, 1,555,067 tok (1,553,370 in, 1,697 out, 1,522,816 cached), 212.1s, $0.2303596)
  - COND_RATOR normalizes conditional continuation application; split actual remaining guard, simplify assert; replace obsolete cg<=dg+mc with caller post-credit bound; supply charged saved-account equality and err witness for call_returns_summary. -> normalize_entry, compose_entry and Finalise call_entry_prepared checked. Build advances through finite SPEC helpers to downstream caller_observation_frame missing state-gas observations. Full target not clean. (`TO_seq58_progcall_port-20261031T211644Z_m1717_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T211644Z_m1717_t001` (use `read_tool_output` for exact output)

## C1.5

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0058`
- blocker: 
- actual effort: 1 sessions, 8 steps, 7 tools, 2 holbuild, 976,532 tok (974,926 in, 1,606 out, 961,536 cached), 125.4s, $0.1389936
- next: Review bounded C1.5 closure and authorize commit; C1.6 must restate both exports and validate shared tactics against actual new semantic meter relations.

### Attempts / Evidence

- `E0057` (progressed, plan_incomplete, actual effort: 1 sessions, 1 msgs, 5 steps, 4 tools, 1 holbuild, 567,133 tok (566,543 in, 590 out, 555,904 cached), 43.5s, $0.0827684)
  - Added all four state-gas observation equality conditions to caller_observation_frame; built target. -> Frame theorem now checked without proof tactic changes. IMP finite conversion helpers also check unchanged. Build reaches SPEC_Call_any, whose old precondition cannot instantiate new call_entry_prepared. (`TO_seq58_progcall_port-20261031T211644Z_m1727_t001`)
- `E0058` (proved, , actual effort: 1 sessions, 8 steps, 7 tools, 2 holbuild, 976,532 tok (974,926 in, 1,606 out, 961,536 cached), 125.4s, $0.1389936)
  - Ported caller_observation_frame to four meter observations, proved call_final_context_observations by failed cases, prepared shared entry to name exact final context and derive non-meter observations, post uses context boundary/meter lemmas. -> Checked prefix through both local theorem proofs and ML tactic declarations. Target fails at first obsolete SPEC_Call_any as expected by repaired PLAN. Actual shared tactic application remains unvalidated pending C1.6 restatement; no full-target claim. (`TO_seq58_progcall_port-20261031T211644Z_m1738_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T211644Z_m1738_t001` (use `read_tool_output` for exact output)

## C1.6

### Current Status

- result: `progressed`
- diagnosis: `missing_helper`
- latest episode: `E0059`
- blocker: Meter boundary application interface not aligned to simplified prepared-entry output; large shared tactic proof state.
- actual effort: 1 sessions, 3 msgs, 40 steps, 39 tools, 9 holbuild, 3,136,374 tok (3,126,361 in, 10,013 out, 3,023,744 cached), 611.6s, $1.0842392
- next: Escalate interface quality to strategist rather than add more manual existential instantiations or copy large assumptions.

### Attempts / Evidence

- `E0059` (progressed, missing_helper, actual effort: 1 sessions, 3 msgs, 40 steps, 39 tools, 9 holbuild, 3,136,374 tok (3,126,361 in, 10,013 out, 3,023,744 cached), 611.6s, $1.0842392)
  - Retain entered child's charged bit in call_entry_prepared; prove call_final_context_meters by semantic settlement unfolding in local boundary -> Both checked: latest builds pass these theorems. Boundary initially used conjunctive call_return_context_meter as rewrite, which did not fire; direct settlement unfolding inside this boundary works. (`TO_seq58_progcall_port-20261031T211644Z_m1766_t001`)
  - Restate both exports exactly per new strategist meter-carrier statement; reconstruct aliases in shared entry after SIMP_RULE -> Statements parse. Inline entry diagnostic verifies drule_all prepared-entry succeeds. SIMP_RULE eliminates success/out/gasLeft existentials and normalizes caller into updates; old shared framing tactic had never handled this. New alias reconstruction checks non-meter observations but meter helper backward application leaves uninstantiated variables and fails. (`TO_seq58_progcall_port-20261031T211644Z_m1782_t001`, `TO_seq58_progcall_port-20261031T211644Z_m1791_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T211644Z_m1766_t001` (use `read_tool_output` for exact output)
- `TO_seq58_progcall_port-20261031T211644Z_m1782_t001` (use `read_tool_output` for exact output)
- `TO_seq58_progcall_port-20261031T211644Z_m1791_t001` (use `read_tool_output` for exact output)

## C1.6.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0060`
- blocker: 
- actual effort: 1 sessions, 2 msgs, 24 steps, 23 tools, 10 holbuild, 2,686,464 tok (2,679,163 in, 7,301 out, 2,622,720 cached), 415.3s, $0.4481680
- next: Review bounded closure, authorize checkpoint commit despite known downstream export failure as previous boundaries; C1.6.2 replace experimental tactic with opaque wrapper consumption.

### Attempts / Evidence

- `E0060` (proved, , actual effort: 1 sessions, 2 msgs, 24 steps, 23 tools, 10 holbuild, 2,686,464 tok (2,679,163 in, 7,301 out, 2,622,720 cached), 415.3s, $0.4481680)
  - Introduce opaque call_entry_ready and wrapper with exactly prepared-entry premises; apply checked entry and observation/meter boundaries forward -> Wrapper checks. Clear input premises immediately after entry elimination to keep symbolic context small. A small Boolean carrier normalization supplies exact forward meter premise. Normalize each result assumption independently (not fs against entire context), unfold ready predicate, split and close trivial packaging conjuncts. (`TO_seq58_progcall_port-20261031T211644Z_m1817_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T211644Z_m1817_t001` (use `read_tool_output` for exact output)

## C1.6.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0062`
- blocker: 
- actual effort: 1 sessions, 2 msgs, 32 steps, 31 tools, 8 holbuild, 2,220,262 tok (2,217,969 in, 2,293 out, 2,156,416 cached), 218.3s, $0.3616776

### Attempts / Evidence

- `E0061` (progressed, other, actual effort: 1 sessions, 2 msgs, 11 steps, 10 tools, 2 holbuild, 1,478,616 tok (1,477,443 in, 1,173 out, 1,358,720 cached), 83.1s, $0.3850480)
  - Replace experimental shared entry with normalized opaque wrapper, explicit existential elimination, one predicate elimination -> Entry application now checks in SPEC_Call_any and reaches Resume post. REWRITE_RULE predicate elimination left beta-redex from let and did not unpack; SIMP_RULE (srw_ss()) [call_entry_ready_def,LET_THM] fixed this. All old reconstruction blocks removed. (`TO_seq58_progcall_port-20261031T211644Z_m1828_t001`)
  - Run existing shared post tactic with newly appended meter witnesses -> Fails with goal not an exists during witness selection. Exact inner stage not yet isolated. Shared post still uses legacy simp/SEP_EXISTS conversion and semantic unfolding; must inspect after conversion before changing witnesses or formulas. (`TO_seq58_progcall_port-20261031T211644Z_m1828_t001`)
- `E0062` (proved, , actual effort: 1 sessions, 2 msgs, 32 steps, 31 tools, 8 holbuild, 2,220,262 tok (2,217,969 in, 2,293 out, 2,156,416 cached), 218.3s, $0.3616776)
  - Inspect converted post and remove final's implementation equality before post/frame simplification; preserve merged while simplifying projections -> Legacy failure was a residual parsed-code conjunction caused by expanding final before using final.msgParams projection. Dropping final equality enables interface rewrites; IgnAsm merged prevents meter expression expansion during separation normalization. Both exports now share checked entry/post/frame tactics without semantic unfolding. (`TO_seq58_progcall_port-20261031T211644Z_m1852_t001`, `TO_seq58_progcall_port-20261031T211644Z_m1868_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261031T211644Z_m1868_t001` (use `read_tool_output` for exact output)

## C1.8

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0010`
- blocker: 
- actual effort: 1 sessions, 11 steps, 10 tools, 4 holbuild, 1,080,488 tok (1,078,071 in, 2,417 out, 1,061,888 cached), 417.0s, $0.1627248
- next: Review C1.8 and allow C1.3. Note C1.3 call_exn_safe_step_call universally quantifies over merely nonempty contexts, so original checked counterexample still disproves this local helper; exported guard alone does not repair broad helper. Need invariant-specific safety decomposition rather than merely matching current consume_gas goal. Consider shallow C1.3 redesign before execution.

### Attempts / Evidence

- `E0010` (proved, , actual effort: 1 sessions, 11 steps, 10 tools, 4 holbuild, 1,080,488 tok (1,078,071 in, 2,417 out, 1,061,888 cached), 417.0s, $0.1627248)
  - Validate current source boundary prefix via vfmProgCallTheory build; add charge and post-credit abort equations, and update failure normalization to credit on both balance and depth branches. -> call_charge_new_account_pair and call_credit_abort_pair check both charged/uncharged cases, exact meter and normal return under post-credit bound. call_entry_failure_normalize now matches actual credited semantics. Builds pass all these plus proceed_call_pair, pop_and_incorporate_context_pair and handle_exception_memory_return, stopping only at pre-existing call_exn_safe_step_call in C1.3. (`TO_seq58_progcall_port-20261030T183500Z_m0281_t001`, `TO_seq58_progcall_port-20261030T183500Z_m0283_t001`)

### Evidence refs

- `TO_seq58_progcall_port-20261030T183500Z_m0283_t001` (use `read_tool_output` for exact output)
