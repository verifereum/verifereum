# PLAN

## Structured Components

### C1: Port the callee-agnostic CALL contract and its prerequisite machinery
- Kind: `unprovability_gate`
- Risk: 5
- Work priority: 10
- Work units: 0
- Rationale: Suspected theorem falsehood: complete probe components under C1 (including C1.2.2) before any other proof work. If probes confirm a counterexample, stop/report unprovable; do not silently repair the theorem.
- Required for completion: yes
- Checkpoint: yes

#### Summary
Port only prog/vfmProgCallScript.sml and strictly necessary prog-local interfaces. Preserve the five exported contracts except for the mandated state-gas dimension. Build and check boundary machinery and the three shared tactics before starting either exported CALL proof. Retain callee-independent finite termination, rollback and stipend guarantees. Finish with the specified clean, warning-free build and commit.

#### Not to try
Do not use SPEC_Call or step_call_prepared directly as if they covered failed balance/depth checks. Do not preserve the old call_gas cost argument, or silently assume gasLeft alone accounts for spill repayment. Do not hide creation cost in an abbreviation, add callee hypotheses, change lower theories, or repair unrelated repository obligations. No cheats, axioms, mk_thm, or TRY/ORELSE proof-search fallbacks.

#### Argument
The existing argument has three layers: normalize one CALL into immediate failure or child entry; obtain a finite return of arbitrary child code in a Collect domain using the existing run_call machinery; convert the returned caller observation into a separation-logic SPEC with an unchanged outside frame. State gas must follow actual semantic transitions at each boundary, not be treated as an unchanged frame field. A reservoir-covered creation charge does not spill, entry drains the remaining reservoir, failure restores the child's meter before absorbing and crediting the creation charge, and success absorbs then repays spill. These operations can also change execution gas, so the final execution-gas expression must include their forced effect rather than reusing the old gasUsed equality blindly. The stipend proof continues to restrict account-changing instructions by their execution-gas sentries; it must not assume the absence of state gas. No balance, depth, callee-code or extra initial-meter invariants may be introduced into exported assumptions.

#### Definition design
Keep the existing semantic definitions unchanged. Use local boundary equations whose conclusions are execution-result pairs and explicit context transformations, consumable by drule rather than manual theorem plumbing. Express return meters with absorb_state_gas and repay_state_gas_spill_context, and expose small equations for charge_new_account, credit_new_account, restore_state_gas and drain_state_gas_reservoir as necessary. Probe both charged/uncharged and success/revert/exception/no-entry paths before propagating these interfaces. The root's original meter may have nonzero spill and committed quantities: do not specialize them away. If an exported frozen non-meter guarantee fails, obtain a concrete checked counterexample and stop with the tightest sufficient fix, without applying it.

#### Code structure
Keep local logical helpers in prog/vfmProgCallScript.sml adjacent to the existing boundary and exception-safety families. Keep the three shared ML tactics after the logical interface and before SPEC_Call_any; extract only genuinely reusable ML code into a prog-local library if needed, not logical facts. Existing suspended subproofs may remain, but hard timed units should become named local lemmas. No spec/ or configuration changes. Build only through holbuild, with the prescribed heap/jobs and no tactic-timeout override.

### C1.1: Check primitive frame-boundary equations and their immediate prefix prerequisite
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 8
- Rationale: The reported prefix failure is a concrete missing normalization of get_accounts and drain_state_gas_reservoir, not failure of the structural invariant. The remaining boundary equations are bounded semantic unfoldings.
- Checkpoint: yes
- Progress transition: `refinement`

#### Progress note
Extend the existing boundary-equation obligation only with repair of step_push_TL_TL, needed to reach those equations in source order. Baseline evidence TO_seq58_progcall_port-20261030T170049Z_m0009_t001 proves no theorem and no prior proof credit is claimed. C1.2 retains its subsequent infrastructure recheck.

#### Summary
First repair step_push_TL_TL's CREATE branch so the theory can reach the boundary lemmas. Preserve that theorem's statement and all exported contracts. Port and check call_abort_pair, call_entry_failure_normalize, proceed_call_pair, pop_and_incorporate_context_pair and handle_exception_memory_return against the state-gas semantics. Keep meter calculations at these boundaries so subsequent structural and rule proofs can consume equations rather than repeat semantic unfolding.

#### Description
The only newly authorized structural repair is prog/vfmProgCallScript.sml:42–56, step_push_TL_TL. Its residual goal and assumptions already identify the missing interface: assumptions get_accounts u = (INL accounts,s'') and drain_state_gas_reservoir s'' = (INL reservoir,s'³') must imply equality of context tails. If direct bounded simplification is unwieldy, a local helper stating that successful drain preserves TL of contexts is owned by this component and may be placed immediately before step_push_TL_TL. Port the listed boundary equations with explicit state-gas effects, including the new proceed_call parameters and initial_context fields. Validate success, revert, exceptional failure and no-entry paths separately. Checking this component means the repaired prefix and boundary equations compile; later consumers remain the responsibility of their existing components.

#### Statement
Preserve step_push_TL_TL exactly: wf_state s ∧ step s = (r,s') ∧ LENGTH s.contexts < LENGTH s'.contexts ⇒ LENGTH s'.contexts = SUC (LENGTH s.contexts) ∧ TL (TL s'.contexts) = TL s.contexts. Boundary equations remain local and may be restated to expose the actual state-gas transitions; no exported non-state-gas hypothesis may change.

#### Approach
Repair the existing CREATE-branch normalization in step_push_TL_TL by including get_accounts_def and drain_state_gas_reservoir_def and the current-context getter/setter equations they use: get_accounts leaves the state unchanged, and draining changes only the head context, hence TL s'³'.contexts = TL u.contexts = TL s.contexts. Then retain the original boundary-equation work: follow the concrete charge/credit, drain, absorb/repay and exception-restoration sequence from the semantics, express record updates using those meter operations, and prove each local equation separately before its consumers. Build incrementally; if another earlier structural proof blocks reaching these equations, report its exact failure rather than silently enlarging this exception to all prefix proofs.

#### Not to try
Do not infer equality of complete context tails from MAP FST and FRONT facts alone; use the actual head-only drain transition. Do not unfold the entire CREATE or CALL execution pipeline to solve this tail goal. Do not move C1.2 ahead by inventing a dependency cycle, or take ownership of every broken prefix theorem. Do not hide failed proof searches with TRY/ORELSE, raise tactic timeouts, or weaken the frozen exported rules.

### C1.2: Verify suspected CALL refund counterexample before resuming infrastructure
- Kind: `unprovability_gate`
- Risk: 5
- Work priority: 0
- Work units: 0
- Rationale: The reported creation credit can erase the execution-gas credit required by abort_call_value. The available build failure does not itself prove falsehood, and applicability to the frozen exports must be checked concretely.
- Checkpoint: yes
- Progress transition: `refinement`

#### Progress note
E0003 establishes a genuine invariant/interface concern but not a checked counterexample. Preserve its prerequisite edits as partial work, not as certification of exception safety.

#### Summary
Block ordinary proof work pending concrete verification. First check the no-entry CALL and its Impossible result. Then check whether the same state satisfies the frozen exported preconditions. Do not add zero-spill or other repair hypotheses.

#### Approach
Run only the gate probes until resolved. If export falsehood is confirmed, stop with concrete evidence and the tightest sufficient fix as a proposal only; if it is ruled out, return for replanning the structural safety interface and all consumers.

#### Not to try
Do not continue the old consume/read invariant proof through credit_new_account. Do not assume spill <= gasUsed, zero spill, or reachability without deriving it from the frozen precondition. Do not interpret the current failed tactic as checked falsehood.

#### Argument
The old safety proof maintains stipend <= gasUsed after charging. Creation credit now occurs before stipend unuse and may reduce gasUsed below stipend when incoming spill is unconstrained. A local safety counterexample alone does not refute the exports; the second probe must establish admissibility and the actual SPEC-level obstruction.

#### Definition design
Use the actual charge_new_account, credit_new_account, abort_call_value and unuse_gas definitions as the computation boundary. Concrete probe facts must distinguish returned exceptions from ordinary CALL failure. No semantic definitions or exported contracts may be changed.

#### Code structure
Place checked probes in a prog-local standalone theory importing already-built dependencies, or a checked prefix before the failing theorem. Avoid importing the unbuildable vfmProgCallTheory. Keep all edits within prog/ and use holbuild only.

### C1.2.1: Check concrete no-entry CALL exception
- Kind: `unprovability_probe`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: This is finite evaluation of a specified no-child-entry branch, with no induction or callee execution.
- Checkpoint: yes

#### Summary
Construct a concrete caller with gasUsed=0, stateGasSpilled=183600 and stateGasLeft=183600. Request zero gas, transfer value one to an empty non-precompile address, and give the caller insufficient balance. Check exact charging, refund and abort results in HOL.

#### Statement
Produce a concrete state s and checked evaluation of step_call Call s demonstrating or refuting the claimed Impossible result, with s.contexts <> []; derive failure of call_exn_safe_step_call if the evaluation supports it.

#### Approach
Use one caller frame, a sufficient execution gas limit, a seven-operand CALL stack with zero memory lengths, Collect domain and concrete empty accounts. Compute the actual static/access/delegate costs rather than assuming the approximate 11600; split charge/refund/abort computation into small facts if necessary and record the exact exception payload.

#### Not to try
Do not use a symbolic assumed evaluation or cheats. Do not change semantics to make the example work.

### C1.2.2: Check an admissible non-precompile witness against the frozen CALL contracts
- Kind: `unprovability_probe`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: This is a bounded concrete verification probe, not an assertion that the exported rules are false. The existing checked computations provide the method; the missing non-precompile premise must be checked first.
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0007

#### Progress note
E0007 supplies checked computation methods and establishes that the prior witness is inadmissible. It does not close this obligation or certify exported falsehood; the fresh witness and full SPEC obstruction require new checked evidence.

#### Summary
The 256w witness is inadmissible for both frozen exports because it is a precompile. Retain that result only as helper-level evidence. Test a fresh 100w destination and check every exported premise before attempting a SPEC counterexample. Report export falsehood only with a checked full precondition and semantic obstruction.

#### Statement
Determine whether a concrete CALL state with destination (100w:address) satisfies the complete state-gas-ported frozen preconditions and refutes SPEC_Call_any or SPEC_Call_stipend; alternatively establish precisely why this candidate fails.

#### Approach
Keep the existing 256w probe results and introduce a separately named 100w witness in prog/vfmCallRefundProbeScript.sml, changing all destination-dependent account, stack, access and domain terms consistently. First prove non-membership using precompile_addresses_def, finite_setTheory.fIN_fset_ABS and EVAL with wordsLib, then recheck the Impossible computation, step dispatch, guarded FUNPOW result and every arithmetic/delegate/state-gas premise. Only if these checks pass construct the full separation-logic precondition and prove the SPEC obstruction using the actual model semantics; if any check fails, report that failure without claiming exported falsehood.

#### Not to try
Do not reuse 256w as an exported-rule counterexample, omit the explicit non-precompile premise, or infer SPEC failure from helper safety failure alone. Do not modify frozen exports or files outside prog/. The existing spec/prop probe is reference evidence only, not an edit target. Do not add assumptions to make the frozen rules true.

### C1.3: Port stipend preservation and finite child-return observations
- Kind: `proof`
- Risk: 2
- Work priority: 30
- Work units: 8
- Rationale: The existing stipend cutoff argument remains based on execution-cost sentries; the changed return observation is supplied by the checked boundary equations.
- Dependencies: C1.1, C1.2
- Checkpoint: yes

#### Summary
Recheck the call_stipend_prefix family and all remaining local return infrastructure up to call_returns_summary. Port run_call_memory_returns and call_returns_summary to exact boundary meters. Preserve arbitrary-callee termination, rollback on failure, and originalAccounts/account/toDelete restrictions at stipend. No exported CALL proof starts in this component.

#### Statement
Keep call_returns_summary's finite FUNPOW return, wf_state, Collect domain, txParams, rollback and stipend content. Replace its old final context equation by the state-gas-aware return transformation, with child meter witnesses sufficient to compute the final four state-gas fields and forced execution-gas correction. Cover both no-entry abort and entered execution without adding exported preconditions.

#### Approach
Use the existing finite-run/last-pop decomposition and C1.1's handler equation to obtain the actual returned caller. Reprove stipend preservation along the existing prefix proof: execution-gas sentries rule out account mutations, while meter operations need only their proved account/originalAccounts frame facts. Compose immediate failure separately so credit without drain is represented correctly.

#### Not to try
Do not infer that a stipend child has no reservoir or that parent spill is zero. Do not weaken the stipend originalAccounts frame guarantee or rollback guarantee. If those guarantees genuinely fail, stop with a concrete checked counterexample, not an extra invariant.

### C1.4: Rebuild call_entry_prepared on the charged CALL prefix
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 40
- Work units: 8
- Rationale: The sibling step_call_prepared exhibits the exact charge and arithmetic pattern. The local theorem must additionally normalize no-entry branches, already handled by C1.1.
- Dependencies: C1.1, C1.3
- Checkpoint: yes

#### Summary
Replace deleted new_account_cost and the old call_gas spine. Port call_entry_prepared, including normalize_entry and compose_entry, to creation-charge accounting before gas forwarding. Retain failed balance/depth paths. Check its exact final observation interface before changing exported proofs.

#### Statement
Use newAccountCharged = (op = Call ∧ 0 < value ∧ account_empty ta), stateCost = (if newAccountCharged then new_account_state_gas else 0), and the literal charge ≤ c.stateGasLeft. As in sibling step_call_prepared, call_gas receives remaining gas after static_gas op + access_cost + value cost + delegation cost + memory cost, with its last two cost arguments 0 and 0; total execution cost adds dynamicGas. The prepared caller has stateGasLeft reduced by stateCost; no-entry paths credit it, entered paths drain it. Preserve the existing finite-return and non-meter observations.

#### Approach
Use the checked sibling prefix interface if its exported signature covers the needed continuation; otherwise keep the existing single-bind peel and extract a local normalization lemma covering both balance and depth decisions. Compose that normalization with C1.1 and C1.3, keeping the creation flag determined before value transfer and the charge before 63/64 computation.

#### Not to try
Do not copy the sibling theorem's sufficient balance/depth hypotheses into this statement. Do not reuse the old call_gas_charged_bound without checking its new argument interpretation. Avoid a large concrete qexists/qspecl interface: specialize the prefix into a local lemma whose conclusion matches the normalization use site.

### C1.5: Check observation framing and shared tactic machinery
- Kind: `proof`
- Risk: 2
- Work priority: 50
- Work units: 5
- Rationale: Framing is a finite observation-constructor case split and SPEC conversion already has a short semantic proof.
- Dependencies: C1.4
- Checkpoint: yes

#### Summary
Prove the state-gas extension of caller_observation_frame and retain IMP_EVM_SPEC_FINITE and IMP_EVM_SPEC_FINITE_CODE. Update call_spec_entry_tac, call_spec_post_tac and call_spec_frame_tac against the checked entry/return interfaces. Exercise the tactics on a local boundary-to-observation smoke lemma before starting exported rules. This checkpoint enforces the TASK's machinery-first requirement.

#### Statement
caller_observation_frame gains exactly the four missing outside-domain implications: absence of each state-gas observation implies equality of that corresponding caller field. Its other premises and conclusion remain unchanged. IMP_EVM_SPEC_FINITE and IMP_EVM_SPEC_FINITE_CODE retain their exact existing statements. The local smoke lemma translates a C1.4 result into the owned observation conjunction and outside-domain equality, including all four meter observations.

#### Approach
Extend the existing evm2set constructor case split and separation rewrites to the state-gas atoms. Parameterize post witnesses for child/result meter quantities and use the semantic context transformation from C1.4 rather than re-unfolding meter semantics inside ML tactics; compile and prove the local smoke lemma with all three shared tactics.

#### Not to try
Do not begin either exported CALL proof before this checkpoint is checked. Do not solve missing observation coverage by owning unrelated frame resources or adding non-state-gas premises.

### C1.6: Restate and prove SPEC_Call_any and SPEC_Call_stipend
- Kind: `proof`
- Risk: 2
- Work priority: 60
- Work units: 5
- Rationale: Once the shared machinery is checked, these are separation-logic packaging of the same finite caller-return observation, with and without the stipend specialization.
- Dependencies: C1.5
- Checkpoint: yes

#### Summary
Port both exported contracts with all four meter atoms in pre and post. Use the mandated charge triplet and literal execution-cost arithmetic, with no new_account_cost. Preserve arbitrary-callee and stipend-specific rollback/account guarantees and originalAccounts ownership differences. Prove using the already checked shared tactics.

#### Statement
Keep the names SPEC_Call_any and SPEC_Call_stipend and their current non-state-gas content. Add evm_StateGasLeft, evm_StateGasSpilled, evm_StateGasBaseline and evm_StateGasCommitted, with final values described by the semantic boundary transformations established above. Use newAccountCharged = (call_inst = Call ∧ 0 < value ∧ account_empty toAccount), stateCost = (if newAccountCharged then new_account_state_gas else 0), and (if newAccountCharged then new_account_state_gas else 0) ≤ sg. Write out the sibling execution arithmetic, and include only meter-forced corrections to gasUsed. Retain gasLeft's child-budget meaning rather than hiding parent spill repayment in an enlarged gasLeft witness.

#### Approach
First compare each restated cond and non-meter postcondition against the original source, documenting each change as state-gas forced. Instantiate the checked post witnesses and frame tactic for each rule; stipend must still frame originalAccounts, whereas any owns it existentially. Any false frozen guarantee requires a checked concrete counterexample and a proposed tight fix only, not a changed contract.

#### Not to try
Do not add success-only, sufficient-balance, bounded-depth, code, zero-spill or zero-committed assumptions. Do not conflate a semantic execution-gas repayment with ordinary callee unused gas to preserve an invalid old bound.

### C1.7: Final build, contract audit and clean commit
- Kind: `build_probe`
- Risk: 1
- Work priority: 70
- Work units: 2
- Rationale: This is deterministic certification of the completed scoped port and repository constraints.
- Dependencies: C1.6
- Checkpoint: yes

#### Summary
Run the exact requested theory build and inspect warnings. Audit all five exported statements and all local proofs in the target file. Ensure only prog/ changes and commit them with the exact required trailer. Finish with clean git status.

#### Approach
Run `holbuild --max-heap 12000 -j8 build vfmProgCallTheory` from the repository root, without tactic-timeout overrides; a whole-build timeout may be retried with a larger wall-clock allowance up to 3600 seconds. Check no cheats, axioms, mk_thm, parser warnings or TRY/ORELSE proof-search fallbacks were introduced, no file outside prog/ changed, and no frozen guarantee was lost. Commit with a code-specific message ending exactly `Co-Authored-By: Claude Code <noreply@anthropic.com>\nBot: deepseek (DeepSeek V4.1 Flash)` and verify clean git status.

#### Not to try
Do not run Holmake, hol4-mcp, --holdir, or the Ethereum test suite. Do not change tactic_timeout or stop processes by name; stop only owned jobs by PID.
