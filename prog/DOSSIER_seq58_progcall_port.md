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
