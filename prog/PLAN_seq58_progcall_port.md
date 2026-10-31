# PLAN

## Structured Components

### C1: Complete the CALL port under the explicitly amended contract
- Kind: `proof_group`
- Risk: 3
- Work priority: 0
- Work units: 0
- Rationale: Derived from child component C1.3 risk 3. Existing call_exn_safe_step_call asserts unconditional nonempty-context safety, already refuted by historical checked refund witness. Owner-authorized export guards do not repair this universally quantified local helper or its step_inner/run_call consumers.
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

### C1.3: Design and validate callee-prefix safety before finite-return integration
- Kind: `proof_group`
- Risk: 2
- Work priority: 20
- Work units: 0
- Rationale: Only bounded interface probes are authorized in this revision. Their outputs are checked lemmas or precise residual obligations, not an assertion that the proposed invariant is already preserved.
- Dependencies: C1.8
- Checkpoint: yes
- Supersedes: C1.3
- Progress transition: `replacement`
- Carries progress/evidence from: E0011

#### Progress note
Retain E0011's diagnosis of false unrestricted safety, not proof credit. No prior proof of this component is carried forward.

#### Summary
Replace nonempty-only opcode safety by an invariant on executing callee frames, never on the suspended external caller. Test initialization, refund margins, nested push/pop, and the final pop separately. Existing wf_state does not imply spill<=gasUsed. Probe completion requires a strategy checkpoint and a further plan before finite-return consumers are authorized.

#### Not to try
Do not prove call_exn_safe_step_call from nonempty contexts. Do not derive spill backing from wf_context or wf_state. Do not require EVERY meter_ok over the complete context stack. Do not use large manual theorem instantiations to hide a missing invariant, or treat a probe build as certification of the return summaries.

#### Argument
A fresh entered callee has zero spill and committed charge. Internal execution must preserve sufficient execution-gas backing for refundable meter balances and for outstanding descendant grants. The protected suffix starts at the suspended caller; its meter need not satisfy the callee invariant. Internal pops return to a protected callee and must preserve the invariant; the final pop returns to the external caller and needs only the exact semantic return equation, not preservation of the callee invariant. Termination should reuse existing run_call trace/termination results if their hypotheses can be established without restricting that external caller. This is a candidate argument to test, not a claim of an already proved invariant.

#### Definition design
Use a predicate parameterized by entry depth n, selecting TAKE (LENGTH s.contexts - n + 1) s.contexts while n<=LENGTH s.contexts. Start with refundable backing c.stateGasSpilled+c.stateGasCommitted<=c.gasUsed for selected frames. Test whether suspended selected frames require the stronger margin: their own refundable backing plus the sum of descendant (gasLimit-gasUsed+stateGasSpilled+stateGasCommitted) is <= their gasUsed. Do not include the external caller at index LENGTH s.contexts-n+1. At the final pop the predicate is no longer required. Keep this separate from wf_state: wf_context_def has no spill bound, and gas_stack_ok_def includes descendant spill but not the parent's own spill or committed balance. Probe these distinctions explicitly before adopting a definition.

#### Code structure
All new lemmas and probes belong in prog/, preferably a temporary standalone probe theory importing unchanged property theories, then migrate accepted durable interfaces into vfmProgCallScript.sml. Do not edit spec/. Keep the existing primitive safety combinators. Do not introduce cheats to force the main script through its false theorem. The checkpoint must assign remaining preservation, finite-return, stipend, and summary proofs as executable leaves.

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

### C1.3.3: Validate finite-run consumers and specify remaining proof obligations
- Kind: `diagnostic`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: A bounded signature and use-site audit with small entailment probes determines the exact induction interface before committing to large preservation proofs.
- Dependencies: C1.3.2
- Checkpoint: yes

#### Summary
Check termination and finite-trace reuse against an arbitrary suspended caller. Produce exact replacement signatures for restricted step safety and finite returns. Require a new subtree plan covering preservation and all summaries before allowing downstream execution.

#### Description
The checkpoint deliverable lists replacements for call_exn_safe_step_call, call_exn_safe_step_inst, call_exn_safe_step_inner and step_inner_not_impossible_unimplemented; the nonempty-only versions must be removed/restricted during the subsequent implementation phase. Also account for step_collect_ge2_inl, run_call_collect_inl/returns, call_memory_final_pop, stipend-prefix preservation/footprint, run_call_memory_returns and call_returns_summary, including state-gas return equations. Audit run_call_reaches_outer_contexts and metadata consumers against the unchanged suffix: frame boundaries drain the parent at entry, but the suffix below the active callee must stay fixed during its run. Report whether existing termination can be reused directly or needs a prefix-only measure theorem. This diagnostic cannot close the original C1.3 proof obligation; submit its checked output for replacement with implementation leaves.

#### Approach
Inspect run_call_eq_tr, run_call_finite_trace, run_call_reaches_inv and the current wf/stack preservation uses; prove the initialization entailments their hypotheses need, or report the exact caller-dependent residual. Formulate step safety from selected-head backing and a reached-prefix invariant, then separate internal transitions from the final pop using run_call_last_pop's length argument.

#### Not to try
Do not authorize exported rules after these probes alone. Do not insert an unproved reachable-prefix hypothesis into a finite-return lemma without also scheduling and proving initialization and transition preservation. If a frozen exported contract itself is contradicted, stop with a checked concrete counterexample and the tightest sufficient fix, without applying that fix.

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
