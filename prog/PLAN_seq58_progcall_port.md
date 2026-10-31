# PLAN

## Structured Components

### C1: Complete the CALL port under the explicitly amended contract
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The persisted owner-amendment ruling is authoritative evidence and has not been withdrawn. The invalid unrestricted local safety claim is replaced by scoped prefix safety initialized in a fresh child, with explicit boundary and preservation obligations.
- Required for completion: yes
- Progress transition: `refinement`

#### Progress note
Preserve the narrow amendment authorized in TO_seq58_progcall_port-20261030T183500Z_m0272_t001. E0009 continues to refute the original contract; no new permission to weaken exports is inferred.

#### Summary
Retain only the already-authorized reservoir cover, creditBack = MIN stateCost sp, and calleeGas <= g + gasCost - creditBack amendment. All other exported content remains frozen except for the required state-gas port. Preserve historical counterexamples and checked boundary work. Build scoped callee safety before entry, framing or export proofs. The existing C1.4-.7 dependency path remains in force.

#### Not to try
Do not reopen the original counterexample against the authorized replacement. Do not add backing conditions on the external caller, sp=0, callee-code restrictions or further export guards. Do not use unrestricted nonempty-context CALL safety. No timeout overrides, TRY/ORELSE proof search, or edits outside prog/.

#### Argument
Never-entered calls use the checked guarded charge/credit equation. Entered calls initialize a budget over the fresh callee and its descendants, excluding the external caller; this budget pays internal refunds and forbids impossible inner operations. Unconditional run_call totality plus scoped non-abort safety gives a finite ordinary return. Exact semantic restore/forfeit/absorb/credit/repay equations describe the final meters; observation and stipend results then feed the existing prepared-entry and SPEC machinery.

#### Definition design
Use call_meter_claim = remaining execution gas + spilled + committed as the budget currency. Exclude suspended external frames and discharge the budget after the root returns. Keep final meter transforms context-valued and separate actual refundable gas bounds from reservoir fields. New helper preconditions must be discharged at fresh entry, never exported as extra hypotheses.

#### Code structure
All changes stay under prog/. Keep reusable local budget infrastructure in a prog theory if separation improves build isolation, importing existing spec theories unchanged. Keep semantic boundary lemmas before finite-return consumers in vfmProgCallScript.sml. Preserve checked probes and audit as evidence. Finish via existing C1.7 build/audit/commit obligations and required commit trailer.

### C1.1: Retain checked primitive-boundary progress
- Kind: `historical_evidence`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: This records existing evidence, not new executable work.
- Supersedes: C1.1
- Progress transition: `reclassified`
- Carries progress/evidence from: E0001

#### Progress note
Retain the prior primitive equations and prefix-normalization progress; current-source validation is assigned separately, without granting automatic continuity to changed statements.

#### Summary
E0001 checked primitive boundary equations and the immediate prefix prerequisite. Preserve that source work. Its evidence does not certify newly restated return or export contracts.

### C1.2: Historical falsehood of the original unguarded contract
- Kind: `historical_evidence`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: The confirmed counterexample is historical evidence under the now explicitly amended task.
- Supersedes: C1.2, C1.2.1, C1.2.2
- Progress transition: `reclassified`
- Carries progress/evidence from: E0004, E0009

#### Progress note
Retain both concrete probe episodes, including the admissible non-precompile witness. Neither is a remaining verification gate after the owner's explicit authorization.

#### Summary
E0009 refutes the original frozen unguarded CALL rules. E0004 supplies the earlier no-entry computation. Preserve these facts and their tight repair rationale; do not characterize the original statement as proved.

### C1.3: Prove scoped callee safety and exact finite-return summaries
- Kind: `proof_group`
- Risk: 2
- Work priority: 20
- Work units: 0
- Rationale: The claim currency is checked at the difficult algebraic boundaries; remaining work is split into list lifting, primitive contracts, opcode transitions, handlers and finite-run consumers instead of one unrestricted safety induction.
- Dependencies: C1.8
- Checkpoint: yes
- Progress transition: `refinement`

#### Progress note
E0012-E0014 remain bounded evidence only. Preserve their unchanged leaves; new descendants own every missing preservation and consumer proof.

#### Summary
Replace the false unrestricted CALL safety chain by a rooted prefix budget. Prove initialization without any external caller condition. Establish primitive and nested frame preservation before all-opcode safety. Use unconditional totality only after proving collection-mode non-abort behavior. Restate final-pop, stipend and return-summary consumers with exact meters before C1.4 may start.

#### Not to try
Do not prove termination again. run_call_eq_tr is unconditional, but does not imply INL. Do not infer full safety from checked arithmetic probes or wf_state. Do not spread large monadic unfolds, copied ASSUME terms or manual conjunction plumbing through opcode and SPEC consumers.

#### Argument
For entry depth n, take the top LENGTH contexts - n + 1 frames. Their total claim is bounded by the initial child grant; each frame's own spill plus committed plus claims of all frames above it is bounded by its gasUsed. A fresh child satisfies this with equality for the ceiling and zero own refundable meter. Execution charges decrease claim, spill charges exchange gas for spill, grants transfer claim to a child, and successful pop conserves combined claim; credits and failure restoration do not increase it. Thus every internal refund is backed. At the last root pop the invariant need not hold on the external caller: bound the actual refund by the entry grant instead, then use the existing caller grant bound.

#### Definition design
Define prefix and budget as in AUDIT_seq58_call_safety.md lines 89-102, including the LENGTH contexts < n exit disjunct. Keep wf_state separate. Provide list-local top-update/push/pop lemmas so opcode consumers never unfold EL/SUM arithmetic. Prove result-state contracts for failed intermediate operations as well as successful operations because handlers run on those states. Ordinary restore_state_gas preserves committed; it is not restore_state_gas_to_entry.

#### Code structure
Place budget definitions and list algebra in prog infrastructure; place semantic primitive contracts adjacent to their current boundary equations. Replace the old local safety consumer chain in vfmProgCallScript.sml rather than retaining a false compatibility lemma. Keep call_returns_summary after finite-return and final-pop facts. Any auxiliary theory must build with HOL4/holbuild and contain no admitted facts.

### C1.3.1: Check initialization and refund-margin interface
- Kind: `definition_probe`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: Finite record computations and natural-number arithmetic; failure is a useful bounded diagnostic rather than a demand to prove an unchecked universal preservation theorem.
- Dependencies: C1.8
- Checkpoint: yes

#### Summary
Test callee-local refundable backing on fresh entry and individual meter operations. Establish the margin needed when credit_new_account precedes abort_call_value. Separate unconditionally safe primitives from composed operations needing a margin.

#### Description
Return checked small lemmas and exact residuals. Primitive credit_state_gas_refund is nonempty-safe even with an oversized spill because subtraction truncates; the falsehood occurs in its composition with later gas-return assertions. Preserve existing reader, setter, return/fail/assert, stack/memory and consume_gas safety lemmas where their current statements remain valid. Audit create/abort composites as well as CALL before treating them as unconditional.

#### Statement
Probe fresh initial_context backing; preservation of sp+sc<=gasUsed by charge_state_gas, credit_state_gas_refund, commit_state_gas, restore_state_gas and restore_state_gas_to_entry on their actual branches. In the no-entry CALL path test: pre-existing sp+sc<=g, creation charging, and successful execution charge sufficient for stipend imply stipend<=gasUsed after credit_new_account.

#### Approach
Use the exact pair equations already checked in C1.8 and the meter definitions, with named intermediate contexts rather than full monadic expansion at consumer sites. Verify arbitrary original caller spill is excluded only from this callee-local lemma, not constrained at the export; record any additional arithmetic invariant required by the branch.

#### Not to try
Do not conflate primitive refund exception safety with preservation of the stipend credit margin. Do not change exported statements. If the candidate arithmetic fact fails, provide concrete numerals and request redesign rather than add premises silently.

### C1.3.10: Restate final-pop meter and finite memory-return interfaces
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 70
- Work units: 5
- Rationale: The rooted ceiling bounds actual post-restoration refunds; exact handler equations already isolate the return record.
- Dependencies: C1.3.9
- Checkpoint: yes

#### Summary
Replace old gasUsed-only final-pop equalities with exact semantic context transforms. Bound actual refund after restoration by the root grant. Carry all four state-gas fields through memory return. Do not require external caller backing.

#### Statement
Outputs: repaired call_memory_final_pop and run_call_memory_returns using restore/forfeit, absorb_state_gas, failure credit and success repay_state_gas_spill_context, retaining rollback, memory and control observations. Include actual refund<=cg derived at root depth and the existing cg<=caller.gasUsed premise where required.

#### Approach
Use run_call_last_pop to isolate the final handler, root-depth budget to bound claim, and the C1.3.5/C1.3.8 equations to bound its actual refund. Expose the returned context as a semantic transform and provide simple projection lemmas needed by SPEC consumers.

#### Not to try
Do not state caller.gasUsed-gasLeft as the complete returned meter. Do not bound a pre-restoration gas-left value and silently use it for the post-restoration refund.

### C1.3.11: Port stipend observations and assemble call_returns_summary
- Kind: `proof`
- Risk: 2
- Work priority: 80
- Work units: 8
- Rationale: Existing stipend and frame observations are retained; scoped finite return and exact final-pop meters now supply the missing interfaces.
- Dependencies: C1.3.10
- Checkpoint: yes

#### Summary
Port all stipend-prefix and call_success_safe consumers needed by the exports. Preserve run_call_stipend_originalAccounts and run_call_stipend_footprint observations. Assemble call_returns_summary from guarded no-entry and initialized entered branches. Audit that no stale unrestricted safety theorem or old meter equality remains in the dependency chain.

#### Statement
Outputs include required call_success_safe/call_exn_safe consumers, stipend-prefix preservation through call/pop, run_call_stipend_originalAccounts, run_call_stipend_footprint, and call_returns_summary with exact semantic meters and the authorized guarded abort shape.

#### Approach
Retain the current stipend observation induction, replacing frame-transition peels with boundary lemmas and adding the rooted budget only to internal reachability reasoning where needed. In the entered summary initialize budget from the fresh child without constraining the external caller; in the never-entered branch use C1.8. Check the resulting summary against the existing C1.4 prepared-entry use site before closing.

#### Not to try
Do not weaken stipend account/originalAccounts conclusions or introduce callee-code assumptions. Do not certify C1.3 merely because the probe theory builds; check the actual summary and all its required production dependencies.

### C1.3.2: Check nested-prefix push and pop backing
- Kind: `definition_probe`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: Bounded tests of the two frame-boundary algebraic interfaces reveal whether the candidate needs a descendant budget; no opcode-wide induction is authorized yet.
- Dependencies: C1.3.1
- Checkpoint: yes

#### Summary
Test whether per-frame backing suffices for internal pops. If it does not, test the explicit descendant-budget strengthening in the parent design. Prove fresh-root initialization independently of the suspended caller's meter.

#### Description
The invariant must account for execution gas returned from a child before claiming its parent's spill remains backed. Test committed balance as well as spill, including child failure that restores to entry. Use concrete counterexamples to reject insufficient candidate invariants; these do not by themselves refute an export. Do not initiate full opcode preservation until the checkpoint approves the boundary interface.

#### Statement
Probe root initialization for a fresh callee over an arbitrary caller; internal proceed_call/proceed_create push preservation of selected-frame backing; internal success and failure pop preservation using absorb_state_gas, repay_state_gas_spill_context, restore/credit and the actual execution-gas refund. Separately test final-pop equations without asserting backing of the external caller.

#### Approach
Inspect the actual handle_exception/pop order and calculate each branch on two adjacent selected contexts. Use the property-layer push structures to identify the drained parent and fresh child; derive the exact residual inequality on a suspended selected parent before selecting the invariant definition.

#### Not to try
A per-frame spill bound alone is not automatically closed under subtracting child gasLeft from a parent. The last pop is not an internal-pop preservation case; requiring its caller to satisfy the callee invariant would leak a forbidden assumption.

### C1.3.3: Audit and test the finite-run consumer interface
- Kind: `proof`
- Risk: 2
- Work priority: 30
- Work units: 3
- Rationale: Bounded source/signature inspection and small entailment checks are executable work. This checkpoint chooses a justified invariant and decomposition; it does not assert unchecked opcode-wide preservation.
- Dependencies: C1.3.1, C1.3.2
- Checkpoint: yes
- Progress transition: `refinement`

#### Progress note
Replace the scheduler-skipped diagnostic kind with an executable proof kind. Preserve the original bounded audit obligation, expanding its required report to prevent the group being mistaken for completed finite-return infrastructure.

#### Summary
Inspect the actual finite termination, trace, handler and summary premises. Identify precisely where unrestricted exception safety is consumed. Test whether a callee-prefix refund budget initializes at CALL entry and supplies restoration and nested-return requirements. Deliver exact remaining lemma statements and a dependency map for a mandatory strategy checkpoint; do not start C1.4.

#### Description
Distinguish termination (existence of a run_call result) from successful collection-mode return (ISL and exactly one root pop), since only the latter may require repaired exception safety. Trace call_exn_safe_step_call through step_inst, step_inner and collection-mode safety to identify the smallest affected chain. Account separately for successful pop, REVERT restoration, exceptional forfeit, creation-credit cancellation, and nested CALL/CREATE grants. Check whether reusable invariants already present in the unchanged property theories provide the needed ancestor budget. Report the exact uncovered cases rather than assuming the old wf_state is sufficient.

#### Statement
Required outputs: (1) exact signature/use-site audit of run_call_eq_tr and its total termination basis, run_call_finite_trace, run_call_reaches_inv, run_call_collect_inl, run_call_collect_returns, run_call_last_pop, call_memory_final_pop and call_returns_summary; (2) exact proposed scoped invariant and initialization/preservation/safety/finite-return lemma statements, with every premise traced to entry or an existing checked theorem; (3) bounded checked entailment probes for any newly claimed meter implication, or explicit counterexamples/residual gaps. No full invariant theorem is claimed by this component.

#### Approach
Read the listed consumers and the definitions of the invariants they actually require; build a short premise-to-provider table separating existing checked facts from missing obligations. Use C1.3.1/C1.3.2 interfaces for small arithmetic/record probes of stipend initialization and restoration/forfeit composition, keeping any failed proposed implication out of production consumers. Close with the exact proposed statements and request a scoped PLAN update before checkpoint acceptance: that update must add real proof leaves for each uncovered safety/preservation/finite-summary obligation so C1.4 remains blocked.

#### Not to try
Do not attempt all-opcode induction in this audit. Do not treat a build of the probe theory as a proof of call_returns_summary, or close the parent as complete. Do not copy full assumptions into manually instantiated theorem plumbing to conceal an interface mismatch. Do not add external-caller backing or another non-state-gas premise to the exported contracts.

### C1.3.4: Define and validate the rooted prefix budget interface
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: Finite list arithmetic and fresh-context computation; no opcode reasoning.
- Dependencies: C1.3.3
- Checkpoint: yes

#### Summary
Define the proposed prefix budget using call_meter_claim. Prove fresh-root initialization, top backing and root refund bounds. Supply local update, push and pop lifting rules. These are the only list interfaces semantic consumers should need.

#### Statement
With prefix n s = TAKE (LENGTH s.contexts - n + 1) (MAP FST s.contexts), define budget n cg s by the exit disjunct or SUM claims <= cg and, for each i in prefix, spill_i + committed_i + SUM claims (TAKE i prefix) <= gasUsed_i. Prove fresh initial_context root initialization at n=LENGTH rest+2 with ceiling tx.gasLimit, for arbitrary external caller; active top backing; root-depth claim<=cg; and exit discharge.

#### Approach
Use list induction for top replacement, insertion and removal laws, phrased with scalar claim/margin inequalities as premises. Instantiate fresh-root initialization using call_meter_initial_claim and zero initial usage/spill/committed; test both an internal child pop and root exit before accepting the interface.

#### Not to try
Do not include the external caller in prefix. Do not demand that arbitrary old ancestors are meter-backed.

### C1.3.5: Prove primitive meter contracts on success and error paths
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 8
- Rationale: Existing checked arithmetic covers restore, credit, forfeit and successful pop currency; remaining primitive computations are finite case splits.
- Dependencies: C1.3.4

#### Summary
Expose backing and nonincrease of claim for primitive gas operations. Cover charge failure states and restore/forfeit sequencing. Include drain and grant transfer contracts. Consumers receive meter facts and unchanged-context-tail facts without expanding definitions.

#### Statement
Outputs: result-state backing/claim contracts for consume_gas, charge_state_gas, credit_state_gas_refund, charge_new_account, credit_new_account, restore_state_gas, forfeit_remaining_gas, drain_state_gas_reservoir, and grant/refund operations used by CALL/CREATE. Include returned error states wherever they enter handle_step.

#### Approach
Lift the checked claim algebra from the probe into reusable boundary lemmas. Split MIN and success/error conditions locally; derive exact gas inequalities before lifting through C1.3.4, and distinguish spill-only restoration from full entry restoration.

#### Not to try
Do not assume an operation failed without changing its state. Do not conflate nonincrease of claim with preservation of backing; prove both.

### C1.3.6: Replace unrestricted CALL safety and prove nested entry contracts
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 30
- Work units: 8
- Rationale: CALL and CREATE are finite semantic branches; backing supplies refund safety and the checked stipend-push inequality supplies internal grant margins.
- Dependencies: C1.3.5
- Checkpoint: yes

#### Summary
Restate local step_call safety with top-frame backing. Prove nested CALL and CREATE grant/entry budget transitions, including no-entry and precompile branches. Remove uses of the false merely-nonempty-context implication. Discharge internal refund guards from backing rather than adding export hypotheses.

#### Statement
Outputs: backed-context step_call non-Impossible/non-Unimplemented contract; scoped budget preservation/result-state contracts for step_call, proceed_call and CREATE entry paths, including stipend and failed entry. Include the intermediate-state facts needed by handlers.

#### Approach
Follow current semantic branches and consume the primitive contracts. For pushes use call_meter_stipend_push_budget with actual opcode cost covering stipend; derive post-credit unuse_gas safety from top backing and the semantic grant formula, not from an assumption on the suspended external caller.

#### Not to try
Do not reuse the refuted call_exn_safe_step_call statement. If a branch needs a new export premise, stop and report a concrete witness instead of strengthening exports.

### C1.3.7: Lift primitive and entry contracts to inner execution
- Kind: `proof`
- Risk: 2
- Work priority: 40
- Work units: 8
- Rationale: Finite opcode dispatch using dedicated transition contracts; non-meter operations preserve the budget by context projection.
- Dependencies: C1.3.6

#### Summary
Prove inner execution preserves the rooted budget on its result states. Derive exclusion of Impossible and Unimplemented from scoped backing. Cover all dispatched opcodes, including state-changing and terminal ones. Reuse existing non-CALL safety combinators where their statements remain sound.

#### Statement
For wf_state s /\ budget n cg s /\ 2<=n /\ n<=LENGTH s.contexts, prove the step_inner result-state budget and handler-needed structural facts; if step_inner s=(INR e,t), prove e<>SOME Impossible /\ e<>SOME Unimplemented. Provide corresponding step_inst contracts used by this proof.

#### Approach
Split opcode dispatch into meter-neutral operations, primitive consumers, frame-entry operations and terminal operations. Give any hard opcode its own local named lemma instead of one timed tactic; lift untouched-tail facts via the list boundary interface.

#### Not to try
Do not expand every opcode inside one metis or simplification call. Do not treat collection mode as excluding Impossible; it only supplies the domain-side exclusion.

### C1.3.8: Prove deposit and exception-handler budget preservation
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 50
- Work units: 8
- Rationale: Handler cases are explicit success, revert and exceptional failure; scalar conservation and backing laws isolate the list reasoning.
- Dependencies: C1.3.7
- Checkpoint: yes

#### Summary
Handle code deposit and all exception return branches with actual semantic ordering. Prove internal pop preserves ancestor margins. Discharge the budget after the root pop rather than imposing conditions on the caller. Combine with inner execution to obtain the step-level invariant.

#### Statement
Output: wf_state s /\ budget n cg s /\ 2<=n /\ n<=LENGTH s.contexts /\ step s=(INL (),t) ==> budget n cg t. Supporting outputs cover handle_create and handle_exception from the intermediate-state contracts of C1.3.7, including failure credit after absorb.

#### Approach
Follow handle_create's execution charge then state charge, and handle_exception's restore, optional forfeit, then pop order. For an internal pop use adjacent budget margin to justify unuse_gas and absorb/repay or failure credit; for root exit use the exit disjunct. Preserve exact transform equations for the final-pop consumer.

#### Not to try
Do not assume ordinary rollback clears committed spill. Do not move credit_new_account before absorb: current pop_and_incorporate_context credits the merged parent on failure.

### C1.3.9: Derive collection-mode finite ordinary return
- Kind: `proof`
- Risk: 2
- Work priority: 60
- Work units: 5
- Rationale: Existing unconditional totality, collection preservation and length facts reduce this to invariant propagation and non-abort exclusion.
- Dependencies: C1.3.8

#### Summary
Repair step_collect_ge2_inl and run_call_collect_inl using the rooted budget. Derive run_call_collect_returns with the scoped entry premise. Keep run_call_last_pop reusable without adding unnecessary safety hypotheses. No new termination argument is needed.

#### Statement
wf_state es /\ budget (LENGTH es.contexts) cg es /\ es.msdomain=Collect dd /\ 2<=LENGTH es.contexts ==> ?t dd'. run_call es=SOME(INL (),t) /\ LENGTH t.contexts+1=LENGTH es.contexts /\ t.msdomain=Collect dd'.

#### Approach
Extend the existing run invariant by budget and propagate it with C1.3.8. Use scoped inner non-abort safety, collection-mode domain exclusion and handle_step_not_abort_returns_inl, then unconditional run_call_eq_tr and the existing run_call_inl_length fact.

### C1.4: Rebuild charged call_entry_prepared
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: The sibling prepared-entry theorem supplies the charged spine; no-entry safety and the finite summary have explicit prerequisite components.
- Dependencies: C1.3, C1.8
- Checkpoint: yes
- Progress transition: `refinement`

#### Summary
Remove new_account_cost from the prepared-entry theorem. Add the creation-charge triplet and authorized post-credit bound. Normalize charge before call_gas, then combine guarded no-entry or drained child entry with the return summary. Export an interface directly usable by shared SPEC tactics.

#### Approach
Mirror step_call_prepared in vfmProgScript.sml for literal cost arithmetic and charge placement. Keep normalize_entry as a finite spine peel with access_address_split; compose_entry should consume the new branch boundary lemma and call_returns_summary rather than manually constructing conjunction theorems.

#### Not to try
Do not start exported-rule proofs before this checkpoint passes. Do not recover the old entry spine by treating charge_new_account as an execution-cost summand.

### C1.5: Port observation framing and shared SPEC machinery
- Kind: `proof`
- Risk: 2
- Work priority: 40
- Work units: 5
- Rationale: This is finite observation case analysis and adaptation of existing SPEC conversion proofs to four additional owned meter components.
- Dependencies: C1.4
- Checkpoint: yes
- Progress transition: `refinement`

#### Summary
Check caller_observation_frame with all four meter observations owned. Preserve IMP_EVM_SPEC_FINITE and IMP_EVM_SPEC_FINITE_CODE names and non-meter content. Adapt call_spec_entry_tac, call_spec_post_tac and call_spec_frame_tac to the new semantic return interface. Validate their interface before applying them to exported rules.

#### Approach
Use observation-constructor cases for framing and the existing finite-execution conversion argument for the IMP theorems. Make the post tactic consume projected boundary facts and semantic meter witnesses directly, extracting small projection lemmas locally if needed rather than unfolding the semantic operations at each export.

#### Not to try
Do not leave a changed meter field in the arbitrary frame. Avoid large manual theorem instantiations and MATCH_MP/CONJ plumbing to compensate for a mismatched helper conclusion.

### C1.6: Restate and prove the two narrowly amended exports
- Kind: `proof`
- Risk: 2
- Work priority: 50
- Work units: 5
- Rationale: After checked machinery these are packaging proofs, with the no-entry obstruction explicitly excluded by the authorized guard.
- Dependencies: C1.5
- Checkpoint: yes
- Progress transition: `refinement`

#### Summary
Prove SPEC_Call_any and SPEC_Call_stipend using checked shared tactics. Add the state-gas charge triplet, all four meter resources, creditBack = MIN stateCost sp, and calleeGas <= g + gasCost - creditBack. Keep all other content, including the stipend bound and stronger stipend footprint. State returned meters via the actual semantic transformations, not an invented gas-credit abbreviation.

#### Approach
Copy the sibling literal cost and charge convention, deleting the obsolete creation execution-cost term. Use semantic meter witnesses from call_entry_prepared in post packaging, retaining gasLeft <= calleeGas as a bound on child unused gas only; inspect all newly introduced cond premises against the owner's limited authorization.

#### Not to try
No extra entry balance/depth, spill-zero, caller-account, or callee-code hypotheses. If another obstruction appears, provide concrete checked evidence and stop for owner review; the current exception is not blanket permission to weaken.

### C1.7: Build, audit and commit the completed scoped port
- Kind: `build_probe`
- Risk: 1
- Work priority: 60
- Work units: 2
- Rationale: Deterministic validation after the proof checkpoints.
- Dependencies: C1.6
- Checkpoint: yes
- Progress transition: `refinement`

#### Summary
Run holbuild --max-heap 12000 -j8 build vfmProgCallTheory from the root. Require no parser warnings and no cheats or forbidden proof devices in the file. Audit exported statements against the original contract plus the explicit exception. Commit only prog/ changes and finish with clean git status.

#### Approach
Check the complete theory, not just resumed fragments; allow a wall-clock build timeout up to 3600 seconds without changing tactic_timeout. Review the diff for unintended premise changes and files outside prog/, then commit with the exact task-required Co-Authored-By and Bot trailer lines.

#### Not to try
No Holmake, spec edits, timeout overrides, process-name killing, or Ethereum test-suite runs. A successful build does not replace the statement-content audit.

### C1.8: Check guarded no-entry and meter boundary interfaces
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: These are finite evaluations of existing semantic transformations; the sibling failure rules already expose the required credit arithmetic.
- Checkpoint: yes

#### Summary
Validate the committed primitive equations on current source. Prove a usable guarded credit-then-abort interface for both balance and depth failure. Check entered setup and success/failure return equations with all four state-gas fields. Keep execution refund distinct from child unused gas.

#### Statement
No-entry interface: stateCost <= sg, creditBack = MIN stateCost sp, and calleeGas <= g + gasCost - creditBack imply that credit_new_account followed by abort_call_value/abort_unuse returns normally with the exact semantic meter and unchanged rollback effects. Boundary outputs cover call_abort_pair, call_entry_failure_normalize, proceed_call_pair, pop_and_incorporate_context_pair and handle_exception_memory_return as needed.

#### Approach
Use the sibling guarded failure rules as the arithmetic template and preserve the already checked equations from E0001. Normalize charge and credit once in a boundary lemma; separately normalize drain and failure credit versus success repayment on return, keeping record expressions intact until their projections are needed.

#### Not to try
Do not use the old cg <= caller.gasUsed premise before credit as if it sufficed after credit. Do not collapse creditBack into child gasLeft or claim gasLeft <= calleeGas bounds all meter refunds.
