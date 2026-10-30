# PLAN

## Structured Components

### C1: Complete the CALL port under the explicitly amended contract
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The specific no-entry obstruction has an owner-authorized guard. Existing boundary equations and sibling guarded rules provide the implementation pattern; remaining work is local semantic composition and separation-logic packaging.
- Required for completion: yes
- Supersedes: C1.2
- Progress transition: `replacement`

#### Progress note
The owner explicitly accepted the counterexample and granted the requested exception. E0009 still refutes the original rules, not the guarded replacement. This does not authorize any further weakening.

#### Summary
Continue from the partial port committed as 4dd69a76. Permit only the explicitly authorized reservoir-cover, creditBack definition, and post-credit calleeGas inequality in addition to the state-gas port. Preserve all other exported content. Check the entry, return and framing machinery before starting exported proofs. Stop and report any further necessary hypothesis rather than adding it.

#### Not to try
Do not re-open the original counterexample as a blocker for the authorized guarded rule. Do not infer that the authorized guard alone proves all entered-return branches. Do not add sp=0, balance/depth restrictions, callee-code assumptions, or other new premises. No timeout overrides, TRY/ORELSE proof search, or broad monad unfolding in consumers.

#### Argument
Separate never-entered calls from entered calls. For a never-entered call, charging followed by credit refunds MIN stateCost sp execution gas before unuse_gas; the authorized inequality ensures that the latter cannot produce Impossible. For an entered call, drain the charged caller reservoir into the child and describe return by the exact failure credit/restore or success absorb/repay operations. Existing finite execution and stipend preservation arguments supply termination and callee-independent observations; framing then packages these observations into both SPEC rules.

#### Definition design
Use context-valued semantic meter transformations as the return interface, rather than asserting gasUsed = caller.gasUsed - gasLeft across credit and repayment. Keep child gasLeft bounded by calleeGas separately from meter refunds. Probe both no-entry branches and both child-return outcomes through boundary equations before using the interface in SPEC tactics. Local helper statements may change; exported account, rollback, originalAccounts and stipend claims may not.

#### Code structure
All edits remain under prog/, principally vfmProgCallScript.sml. Keep primitive meter equations near call_abort_pair/proceed_call_pair/handle_exception_memory_return, then preservation/finite-return lemmas, call_entry_prepared, shared tactics, and exports. Reuse sibling vfmProgScript.sml results rather than editing spec/. Keep concrete counterexample evidence clearly labeled as about the original unguarded contract.

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

### C1.3: Port preservation and finite return summaries
- Kind: `proof`
- Risk: 2
- Work priority: 20
- Work units: 8
- Rationale: Existing step/prefix and finite-return arguments are structural; meter changes are isolated by the checked boundary interfaces.
- Dependencies: C1.8
- Checkpoint: yes
- Progress transition: `refinement`

#### Summary
Port remaining exception-safety and stipend-prefix consumers in the file. Update run_call_memory_returns and call_returns_summary to expose exact returned meters. Preserve the stipend account and originalAccounts conclusions. Cover intermediate broken proofs required by these chains, not unrelated theories.

#### Statement
Outputs include the call_exn_safe/call_success_safe consumers required for finite execution, stipend-prefix preservation through call and pop, run_call_stipend_originalAccounts, run_call_stipend_footprint, run_call_memory_returns, and call_returns_summary on the new meter interface.

#### Approach
Follow the existing step and run_call induction structure, using boundary equations at frame transitions. In call_returns_summary split failed from entered explicitly: the former uses the guarded no-entry equation; the latter uses the finite child-return result with drained parent and semantic return meter.

#### Not to try
Do not keep the old caller-with-only-gasUsed-update equality when return also credits or repays state gas. Do not unfold all meter definitions repeatedly in the preservation induction.

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
