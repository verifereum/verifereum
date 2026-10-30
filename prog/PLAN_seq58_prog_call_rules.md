# PLAN

## Structured Components

### C1: Validate shared state-gas proof machinery before repairing frozen rules
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The prefix integration uncertainty is resolved by the checked call_prefix_prog_apply in accepted E0009. Remaining work is finite refund normalization and a bounded audit/validation of existing tail interfaces.
- Required for completion: yes
- Progress transition: `refinement`

#### Progress note
Only parent guidance and risk are revised; completed descendants retain their obligations and accepted episodes.

#### Summary
Validate semantic interfaces independently of the unfinished SPEC theory. The access, meter and arbitrary-continuation CALL prefix are now checked. Finish the refund interface and validate the existing tail normalization vocabulary before attempting frozen rules. Preserve every frozen statement.

#### Not to try
Do not start frozen proofs before machinery validation. Do not broadly unfold bind, access and handlers together, assume charge/refill is identity when sp>0, or raise tactic timeouts.

#### Argument
CALL prefix execution is composition of successful operation equations, leaving the continuation opaque. With stateCost <= sg, charging uses only the reservoir; subsequent credit refunds MIN stateCost sp to execution gas and the remainder to the reservoir. Thus the never-entered path ends with reservoir sg-creditBack, spill sp-creditBack, and execution usage reduced by creditBack and then stipend. Tail handlers must use explicit context equations rather than unfold entire monadic branches inside SPEC.

#### Definition design
Keep the checked prefix wrappers and bridge unchanged. Refund helpers expose concrete head-context updates and preserve all other state fields. Validate existing handler and child-meter interfaces independently before consumers rely on them; any missing semantic boundary discovered by the bounded tail audit must be planned before frozen proofs begin.

#### Code structure
All edits stay in prog/. Use independent probe theories for semantic validation without importing unfinished vfmProgTheory. Keep existing frozen declarations untouched; record tail validation results in the existing CALL_RULES_AUDIT_seq58.md.

### C1.1: Establish statement baseline and shared boundary inventory
- Kind: `definition_probe`
- Risk: 1
- Work priority: 0
- Work units: 3
- Rationale: This is a bounded source audit and computation/interface validation, without changing frozen proofs.
- Checkpoint: yes

#### Summary
Record the frozen theorem-name and statement inventory for the entire file. Check existing gas/refund and access helper signatures against the CALL spine. Inventory all declarations from SPEC_Call_fail_balance to EOF so downstream range coverage is explicit.

#### Approach
Record whitespace-normalized statements before edits and compare SPEC_Call_fail_balance with the TASK verbatim. Inspect the existing state-gas helpers and tail proof dependencies; validate the no-spill charge and refund equations on both charged and uncharged branches, including positive pre-existing sp. Identify the exact shared exception/SELFDESTRUCT/precompile normalization needed by the tail, before attempting its frozen proofs.

#### Not to try
Do not interpret a prior cheat-backed whole-theory build as validation. Do not change statement text to make a helper apply.

### C1.2: Validate CALL prefix through small operation boundaries
- Kind: `proof_group`
- Risk: 2
- Work priority: 20
- Work units: 0
- Rationale: All three children are proved and reviewed; E0009 validates typed opaque transport and the complete generic prefix, eliminating the former integration risk.
- Dependencies: C1.1
- Checkpoint: yes
- Progress transition: `refinement`

#### Progress note
Risk-only strategy release backed by accepted E0009 and commit e55685ad; no changed child obligations or new continuity claims.

#### Summary
The primitive meter equations, meter composition and complete CALL prefix are checked. Preserve the existing access/delegation wrappers and bridge. Consumers should use call_prefix_prog_apply with an opaque continuation rather than reopen the prefix.

#### Approach
Retain all completed children unchanged. Use the accepted generic application equation in subsequent machinery validation.

#### Not to try
Do not reopen completed prefix proofs or unfold their access and meter implementations in consumers.

#### Argument
Each operation yields an explicit successful result and updated state. Typed bind transport composes these equations, and final record normalization reconciles context, rollback and domain updates. The checked application theorem establishes this argument for arbitrary continuations.

#### Definition design
The producer equations and typed call_pop_bind_apply are the proof boundary. call_prefix_prog_apply exposes precisely the final stack, memory, meters, rollback and domain needed by later continuations.

#### Code structure
Keep prog/vfmProgCallPrefixProbeScript.sml and its checked helpers; no further prefix refactoring is required.

### C1.2.1: Small meter operation application equations
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 3
- Rationale: Each equation evaluates a single operation on an explicit nonempty context; arithmetic is confined to one charge guard.

#### Summary
Keep charge_new_account_apply. Add explicit-head-context equations for successful consume_gas, optional static assertion, expand_memory, get_gas_left and get_callee. Validate these individually in the probe theory. Retain the existing access/delegate proofs unchanged unless interface use requires a small wrapper.

#### Statement
Required interfaces: s.contexts=(c,k)::cs /\ c.gasUsed+n <= c.msgParams.gasLimit ==> consume_gas n s = (INL (), s with contexts := (c with gasUsed := c.gasUsed+n,k)::cs); optional static assertion succeeds without state change when doStatic ==> ~c.msgParams.static; expand_memory updates only c.memory to buffer_extend expandBy c.memory; get_gas_left returns c.msgParams.gasLimit-c.gasUsed without state change; get_callee returns c.msgParams.callee without state change. Use actual source operation types and parenthesized record/pair syntax.

#### Approach
Prove each by unfolding only that operation and its primitive getters/setters. Resolve the addition-order guard on a separate scalar subgoal, using arithmetic or a narrowly directed equality; no AC normalization of a monadic continuation.

#### Not to try
Do not combine these into a single large normalization theorem whose proof expands the whole meter spine.

### C1.2.2: Compose the no-spill meter segment
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: Once each operation returns an explicit INL/state pair, composition is finite bind reduction and scalar arithmetic.
- Dependencies: C1.2.1
- Checkpoint: yes

#### Summary
Restore call_meter_segment with the premises from E0002. Compose successful base charge, creation charge, static check, expansion, gas grant charge and sender lookup. Preserve all non-context state fields. Build the probe theory with no failing diagnostic fragment.

#### Statement
call_meter_segment: use the attempted E0002 segment and premises s.contexts=(c,k)::cs, c.gasUsed+baseCost <= c.msgParams.gasLimit, c.gasUsed+baseCost+dynamicGas <= c.msgParams.gasLimit, (if charged then new_account_state_gas else 0)<=c.stateGasLeft, doStatic ==> ~c.msgParams.static, and call_gas value gas (c.msgParams.gasLimit-(c.gasUsed+baseCost)) 0 0=(dynamicGas,stipend). Result is INL(c.msgParams.callee,stipend), with memory extended, gasUsed=c.gasUsed+baseCost+dynamicGas, stateGasLeft reduced by the conditional creation charge; other fields unchanged.

#### Approach
Derive the two required charge inequalities in the exact operand order before unfolding binds. Peel one bind, use its operation equation, reduce its result case, and repeat; use the call_gas premise only after get_gas_left is reduced. Reconcile final update order on a separate record-equality goal.

#### Not to try
Do not simplify arithmetic over unresolved operation applications or branch on their results; the operation equations already establish success.

### C1.2.3: Validate typed opaque transport and compose the CALL prefix
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: Pop, access and metering equations and the bridge already build. The remaining work is composition of success equations; a minimal typed transport check isolates the reported matching problem without unfolding the CALL continuation.
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0008

#### Progress note
Retain the checked wrappers and structural bridge from E0008 as source evidence, not a certificate for the still-unproved prefix application. Replace the unsuccessful forward-transport recipe with a typed opaque diagnostic; the obligation remains prefix composition.

#### Summary
Keep all checked segment wrappers and step_call_prefix_bridge. First validate pop_stack followed by a polymorphic opaque continuation, with the result type present in the goal. Then prove the arbitrary-continuation prefix application by composing pop, memory-info, access and metering success equations. Do not begin frozen rule proofs in this component. Build the probe theory and checkpoint the resulting application lemma.

#### Description
The diagnostic is authorized work within this leaf, not a new descendant or a replacement semantic model. The result type 'a occurs only in the continuation/result, so forward application to a success premise can leave it specialized independently of the use site. Backward application from the typed bind goal avoids that possible mismatch; a direct restricted bind_def reduction avoids transport entirely. Keep the successful diagnostic as a small local lemma only if used by the final proof. Exact types must be taken from the source rather than assuming the illustrative evm_word name exists. If matching still fails on the minimal expression, report that tiny goal and theorem types instead of attempting another full-spine normalization.

#### Statement
First prove a local diagnostic, explicitly typing K : evm_word list -> execution_state -> 'a execution_result (use the actual stack element type from the source):
 s.contexts = (c,k)::cs /\ n <= LENGTH c.stack ==>
 vfmExecution$bind (pop_stack n) K s =
 K (TAKE n c.stack) (s with contexts := (c with stack := DROP n c.stack,k)::cs).
Then prove call_prefix_prog_apply for arbitrary cont under the existing prefix premises: sufficient stack length (6 + vo), vo = if call_has_value op then 1 else 0, named stack operands, max expansion range, access_check/delegate_check, and the exact metering premises of call_meter_prog_apply. Its conclusion is call_prefix_prog op cont s = cont addr value argsOffset argsSize retOffset retSize rb.accounts code charged c.msgParams.callee stipend sFinal, where code is the case expression in call_access_prog_apply and sFinal updates rollback/newDom and the top context's stack, memory, gasUsed and stateGasLeft exactly as the existing apply lemmas specify; all other fields and contexts are preserved.

#### Approach
In prog/vfmProgCallPrefixProbeScript.sml, first prove the minimal displayed pop/opaque-K diagnostic using call_pop_stack_apply and a restricted bind_def rewrite, or backward irule call_bind_success with the continuation/result type fixed by the goal. Check it before composing: if it fails, inspect the actual head constants and types of the goal and transport theorem (monad_bind versus vfmExecution$bind); normalize only that alias, and do not speculate that qualifying the name resolves a type mismatch. For the prefix application unfold call_prefix_prog_def only, keep cont opaque, and peel one outer bind at a time using the checked pop, memory_expansion_info_split, call_access_prog_apply and call_meter_prog_apply equations; use pure_ss with explicit constructor projections/LET_THM and record-update normalization, and close the final continuation equality by congruence/reflexivity. Validate the probe theory with holbuild under the unchanged timeout; record the exact resulting theorem and build evidence for checkpoint review.

#### Not to try
Do not drule a polymorphic success theorem from only the producer equation and expect its conclusion-only result type to match a later continuation. Do not expand access/meter wrapper definitions during composition, invoke broad srw_ss normalization on the whole spine, or expose the concrete balance/depth/proceed continuation. Avoid manual MATCH_MP/CONJ plumbing and quoted copies of large premises. Do not change frozen statements, semantics, tactic timeouts, or files outside prog/.

### C1.3: Validate refund and remaining tail interfaces
- Kind: `proof_group`
- Risk: 2
- Work priority: 30
- Work units: 0
- Rationale: Refund is a direct explicit-state operation equation; tail work is bounded validation of inventoried existing interfaces rather than an unspecified new handler architecture.
- Dependencies: C1.2
- Progress transition: `refinement`

#### Progress note
Decomposes the unstarted bundled leaf into a refund boundary and a tail validation checkpoint. No proved work is invalidated.

#### Summary
First establish refund followed by stipend unuse on a post-charge context. Then validate the existing exception, precompile and SELFDESTRUCT boundary vocabulary in isolation. Missing boundaries trigger a scoped plan update rather than ad hoc frozen-proof attempts.

#### Not to try
Do not combine all tail handlers into one large normalization lemma. Do not treat an inventory or a cheat-backed whole-theory build as semantic validation.

#### Argument
Credit uses MIN against the existing spill, not the amount spilled by the latest charge. The reservoir arithmetic cancels the original no-spill debit except for creditBack. The stipend guard is exactly stipend <= used-creditBack; this allows unuse_gas to succeed after credit. The remainder of the tail should reuse its already explicit restore/forfeit and absorb/repay interfaces.

#### Definition design
Expose refund-plus-unuse as an INL unit/state equation with arbitrary underlying state and head context. Tail validation must identify exact source signatures and build their proof dependencies without the unfinished SPEC rules.

#### Code structure
Place the refund boundary in an independent prog probe theory. Tail validation may extract unchanged helper statements/proofs into a separate prog probe theory; avoid introducing a dependency on unfinished vfmProgTheory.

### C1.3.1: Validate creation refund followed by stipend unuse
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: credit_state_gas_refund and unuse_gas have explicit single-context definitions. Only MIN inequalities and truncated subtraction cancellation are required.
- Dependencies: C1.2
- Checkpoint: yes

#### Summary
Add a reusable equation for the meters after credit and stipend unuse. Cover both charged flags and arbitrary pre-existing spill. Build independently of the unfinished SPEC rules.

#### Statement
Let cost = (if charged then new_account_state_gas else 0), back = MIN cost c.stateGasSpilled, and chargedContext = c with stateGasLeft := c.stateGasLeft-cost. Under s.contexts=(chargedContext,k)::cs, cost<=c.stateGasLeft and stipend<=c.gasUsed-back, prove (do credit_new_account charged; unuse_gas stipend od) s = (INL (), s with contexts := (c with <|gasUsed := c.gasUsed-back-stipend; stateGasLeft := c.stateGasLeft-back; stateGasSpilled := c.stateGasSpilled-back|>,k)::cs). Express these abbreviations with actual HOL let bindings or explicit premises. All other c and s fields are preserved.

#### Approach
Prove the credit operation equation and unuse_gas success equation separately if needed, then compose one successful bind. Isolate (sg-cost)+(cost-MIN cost sp)=sg-MIN cost sp under cost<=sg as scalar arithmetic; use the stipend premise only for the unuse guard.

#### Not to try
Do not assume sp=0 or refund identity. Do not unfold abort handlers or the CALL continuation here; this leaf supplies only their shared meter boundary.

### C1.3.2: Complete independent tail-handler interfaces
- Kind: `proof_group`
- Risk: 2
- Work priority: 50
- Work units: 0
- Rationale: Bounded exact operational equalities separate failure settlement and successful return from SPEC reasoning; no frozen CALL theorem is needed.
- Progress transition: `refinement`
- Carries progress/evidence from: E0011

#### Progress note
Retain the checked nine-helper subset as evidence, not certification of the expanded obligation.

#### Summary
Preserve E0011's independent helper build. Add exact Invalid settlement and general successful return boundaries. Handle Code output separately at the handle_create boundary. Do not prove step_precompile_success_exact during the machinery phase.

#### Approach
Complete the three bounded helper outputs below, then audit consumer coverage. Full step_precompile_success_exact is later frozen-family composition using step_call_prepared, not a prerequisite for declaring independent machinery complete.

#### Not to try
Do not import or re-prove step_call_prepared to validate the tail probe. Do not generalize the zero-refund Memory handle_step lemma to Code without accounting for handle_create. Do not unfold full handlers inside SPEC goals.

#### Argument
handle_step factors through handle_create and handle_exception. InvalidOpcode skips code deposit, restores the child meter, forfeits execution gas, and either leaves an outermost exception or merges the baseline into the parent with account-credit and rollback restoration. Success instead returns unused execution gas, merges state meters, logs and arbitrary refunds, then repays spill; destination-specific stack and memory updates are a separate finite case split.

#### Definition design
Use exact execution-state equalities with premises s.contexts=(child,cb)::(parent,pb)::rest and a named merged context. Keep rollback and all untouched fields explicit via record updates. Success settlement is first stated for handle_exception NONE, not handle_step NONE: Code output can invoke deposit before settlement. Test the empty-return-data Code path needed by SELFDESTRUCT independently. No new generic normalizer is authorized.

#### Code structure
Develop local semantic helpers in prog/vfmProgCallTailProbeScript.sml without importing vfmProgTheory. Keep a source-copy/interface inventory in prog/CALL_RULES_AUDIT_seq58.md. Place corresponding local helpers before consumers in vfmProgScript.sml only after independent validation; frozen proof edits remain deferred until the enclosing machinery phase finishes.

### C1.3.2.1: Exact InvalidOpcode settlement with valid restored child meter
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: The checked residual is exactly the natural-subtraction guard discharged by the restored child meter bound. InvalidOpcode then deterministically forfeits all remaining execution gas, so no parent execution-meter bound is needed.
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0012

#### Progress note
E0012 supplies diagnostic evidence and a retained independent nine-helper subset, not a proof of the Invalid equalities. The failed experimental theorem has already been removed. Correct only auxiliary statements; frozen theorem statements remain untouched.

#### Summary
Add c.gasUsed - c.stateGasSpilled <= c.msgParams.gasLimit to both Invalid handler helpers. Keep the parent unrestricted in execution gas. First rebuild, audit and commit the retained independent tail subset; then prove the corrected Invalid helpers. This does not reopen a frozen-theorem counterexample gate.

#### Description
Scope includes validating the currently retained nine independent helpers in prog/vfmProgCallTailProbeScript.sml, then the two corrected Invalid boundary helpers. Preserve their existing successful proofs. Build that probe theory and audit the stable subset before committing it, using the TASK commit trailer; a stable-subset commit is explicitly allowed before adding the corrected helpers. Final closure needs a checked build of the completed probe and statement audit, not merely the prior residual log. At the consumer boundary document that the new premise is implied by child gasUsed <= gasLimit from the frozen SPEC's well-formed state; if extracting that invariant is not available, report the precise missing interface rather than adding a frozen premise.

#### Statement
Both handle_step_invalid_outermost_exact and the nested Invalid exact-settlement helper must assume `c.gasUsed - c.stateGasSpilled <= c.msgParams.gasLimit` in addition to their context-shape and (for nested settlement) parent-stack-room hypotheses. Outermost conclusion: if `s.contexts = [(c,cb)]`, `handle_step (SOME InvalidOpcode) s = (INR (SOME InvalidOpcode), s with contexts := [(c with <|returnData := []; gasUsed := c.msgParams.gasLimit; addRefund := 0; subRefund := 0; stateGasLeft := c.stateGasBaseline; stateGasSpilled := 0|>,cb)])`. Nested conclusion must retain the exact failed-child absorption and account-credit settlement specified by `pop_and_incorporate_context F`, restore rollback to cb, increment parent pc, push 0w and clear returnData; memory is unchanged because the output is empty. Child stateGasCommitted remains c.stateGasCommitted.

#### Approach
Use handle_create_not_none to bypass deposit handling; normalize restoration, then use the new bound to prove `limit - (used - spill) + (used - spill) = limit` before unfolding the remaining handler. In the nested case the child's remaining execution gas is now zero, so unuse_gas requires no parent bound; absorb baseline and committed fields, apply credit_new_account according to the child's flag, and finish rollback/pc/stack/empty-memory-write normalization.

#### Not to try
Do not retry unrestricted Invalid helpers with larger simplifier sets: the malformed-child case genuinely fails the consume_gas guard. Do not add a parent gas bound, change frozen SPEC statements, or infer an InvalidOpcode counterexample to those statements from this auxiliary omission. Keep restoration/forfeiture arithmetic separate from full handler unfolding; avoid manual theorem plumbing or a giant search tactic. Do not claim E0012 proves the corrected helpers.

### C1.3.2.2: Successful settlement for arbitrary refunds and destinations
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: handle_exception NONE has no charging branch; its return behavior is a deterministic two-destination split.

#### Summary
Generalize successful settlement at handle_exception, not handle_step. Include arbitrary add/sub refunds and both Memory and Code. Supply singleton and inner boundaries needed by SELFDESTRUCT.

#### Statement
Prove local handle_exception_success_outermost_exact: s.contexts=[(c,cb)] ==> handle_exception NONE s=(INR NONE,s). Prove inner Memory and Code projections under s.contexts=(c,cb)::(parent,pb)::rest, c.msgParams.gasLimit-c.gasUsed <= parent.gasUsed and LENGTH parent.stack < stack_limit. Let merged=repay_state_gas_spill_context (absorb_state_gas (parent with gasUsed := parent.gasUsed-(c.msgParams.gasLimit-c.gasUsed)) c.stateGasLeft c.stateGasSpilled c.stateGasCommitted). Both results update parent logs to parent.logs++c.logs, addRefund to parent.addRefund+c.addRefund, subRefund similarly, and pc to SUC parent.pc. Memory mr also sets returnData=c.returnData, pushes 1w, and writes TAKE mr.size c.returnData at mr.offset. Code addr instead sets returnData=[] and pushes w2w addr; memory is unchanged. Rollback is unchanged.

#### Approach
Factor pop_and_incorporate_context T into an exact local equality if needed, then use handle_exception_def for the destination projections. Prove with arbitrary refunds from the outset using update_gas_refund_def; the existing zero-refund Memory helper becomes a specialization rather than the interface for SELFDESTRUCT.

#### Not to try
Do not assert handle_step NONE equals handle_exception NONE for Code output. Do not use a giant SPEC-level rewrite to hide this distinction.

### C1.3.2.3: Empty-output deposit boundary and coverage checkpoint
- Kind: `definition_probe`
- Risk: 2
- Work priority: 30
- Work units: 3
- Rationale: SELFDESTRUCT's empty-output Code case eliminates deposit cost but may still update accounts; a bounded computation exposes the exact state before successful settlement.
- Dependencies: C1.3.2.1, C1.3.2.2
- Checkpoint: yes

#### Summary
Check the empty-output handle_create path for both destinations and compose with the success boundaries. Preserve the validated precompile helper subset and its get_accounts_def fix. Audit all tail consumers without proving frozen rules.

#### Statement
Output local handle_create_empty_output_exact (separate Memory and Code projections if clearer), with c.returnData=[] and explicit nonempty contexts. Code projection must expose update_account addr (lookup_account addr s.rollback.accounts with code := []) s.rollback.accounts, not claim an unchanged rollback. Include any gas bound needed for consume_gas 0 explicitly and show it is available from the SELFDESTRUCT use site. Output an audited map from Invalid, SELFDESTRUCT and precompile consumers to independently built helpers.

#### Approach
Inspect step_self_destruct and its current frozen consumers to check the exact empty-data prestate and gas bound, then evaluate handle_create at empty output, including zero execution/state charge. Build the independent probe theory, propagate only validated helper proof fixes such as get_accounts_def, and record step_precompile_success_exact as deferred C2 composition depending on step_call_prepared; request a scoped C2 update later if its output inventory does not already cover that helper.

#### Not to try
Do not claim zero deposit cost means no account update. Do not certify machinery coverage solely from the nine original helpers, and do not edit frozen theorem bodies at this checkpoint.

### C2: Repair the frozen CALL family
- Kind: `proof_group`
- Risk: 3
- Work priority: 10
- Work units: 0
- Rationale: Derived from child component C2.1.2 risk 3. Native prefix theorem conclusion does not match the frozen consumer's alias-normalized charged-state equality via irule.
- Required for completion: yes
- Dependencies: C1

#### Summary
Repair the five explicitly named frozen CALL obligations using validated machinery. Preserve all statements including step_call_prepared. Cover intervening helper declarations and precompile witness consumers needed by the whole theory.

#### Not to try
Do not use TRY/ORELSE around search, change tactic timeouts, or turn a long residual-goal dispatcher into the shared abstraction.

#### Argument
Apply IMP_EVM_SPEC to expose the concrete state and frame. Normalize precondition abbreviations to field equalities once, apply the common CALL prefix, select the branch using balance or context-count hypotheses, then use its outcome boundary. Successful calls retain the creation charge in the parent and enter proceed_call; never-entered paths use the refund arithmetic. Existing semantic framing and end_tac discharge unrelated resources after record updates are explicit.

#### Definition design
Consumers should use concrete-state prefix/outcome equations and never reopen access/delegation internals. The no-spill premise is essential and already frozen in these rules. If a consumer needs an additional boundary not validated in C1, pause and extend C1 before continuing rule proofs.

#### Code structure
Edit only proof bodies of frozen declarations. Replace the obsolete commented attempted proof/debug dump near lines 4855–4954 as part of the balance proof. Keep helpers local unless existing public use requires otherwise.

### C2.1: Balance and depth failure rules with native prefix machinery
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The missing interface is an equality-result adapter derived directly from the checked prefix equation; no new semantic induction is required.
- Progress transition: `refinement`

#### Progress note
E0019 establishes a consumer matching defect; E0018 native transfer remains unchanged.

#### Summary
Keep the validated native prefix and refund lemmas. Add a result-variable adapter so backward application does not match nested record updates. Validate its use at the balance-rule charged-state goal before completing the balance and depth consumers.

#### Approach
Validate the adapter against the existing balance charged-state equality first. Then reuse this boundary for depth rather than specializing the native theorem manually.

#### Not to try
Do not repeatedly specialize vo and unfold field aliases hoping MATCH_MP_TAC normalizes arithmetic or record expressions. Do not reopen access or metering internals in consumers.

#### Argument
The native prefix equation already computes the charged state. A transitivity adapter moves comparison with a consumer's chosen result from theorem matching into an explicit equality goal, where aliases, arithmetic and record updates can be normalized. Both failure continuations then use the existing refund equation.

#### Definition design
Do not change definitions or frozen statements. Retain call_prefix_prog_apply as the semantic equation. Expose a new boundary with schematic result on its right-hand side and an explicit equality premise relating that result to the native continuation application.

#### Code structure
Place the local adapter next to call_prefix_prog_apply in prog/vfmProgScript.sml. Replace failed specialization plumbing in the balance proof. Keep all changes within prog/ and retain the independently checked native proofs.

### C2.1.1: Transfer and validate native prefix/refund interfaces
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: Source proofs already check independently; rechecking them with existing main constants is a bounded integration task.
- Checkpoint: yes

#### Summary
Copy the validated helper dependency closure, not the duplicate boundary definitions. Preserve existing main symbols and mark new helper theorems local. Check the main build reaches and accepts the entire transferred block before starting failure proofs.

#### Description
The authorized dependency closure includes the access/delegate segments, charge/consume/static/memory/gas-left/callee applications, meter segment, pop-stack and pair/bind helpers, step_call_segments, the named access/meter/prefix programs and their applications and bridges, and refund application. Existing equivalent main lemmas should be reused; when names collide but interfaces differ give the new local helper a fresh name. Do not change any pre-existing theorem statement. If actual boundary definitions differ semantically, stop and escalate instead of inventing transport axioms or modifying the frozen interface. Validation must identify that the new declarations were checked, not merely cite a failed whole-theory exit code.

#### Statement
Provide main-theory versions of step_call_prefix_bridge, call_prefix_prog_apply and call_refund_unuse_apply with the displayed probe statements interpreted using the original vfmProg boundary constants; provide their missing helper definitions and theorem dependencies from the probe.

#### Approach
Inventory the probe declarations against main: reuse matching access_address_split, memory_expansion_info_split and boundary definitions (msdomain_add, accesses_add, access_cost, access_check, delegate_check, memory_cost, memory_expand_by, expanded_memory), transferring only missing dependencies in source order. Recheck definitions for exact agreement rather than relying on names; port the checked proofs without semantic redesign, and run holbuild --max-heap 12000 -j8 build vfmProgTheory, recording explicit acceptance through the final transferred helper even if the untouched downstream proof fails.

#### Not to try
Do not copy the probe header or its duplicate constants, and do not add the probe as an Ancestor. Do not use a temporary cheat in a frozen proof to reach a successful build. Do not mechanically copy all 596 lines without checking existing helper collisions.

### C2.1.2: Prove frozen balance and depth failure rules
- Kind: `proof`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: The new prerequisite validates conclusion matching before these consumers resume; native prefix and refund equations supply the semantic computations.
- Dependencies: C2.1.1, C2.1.3
- Checkpoint: yes
- Progress transition: `refinement`

#### Progress note
E0019 is a valid stuck report, not a proof of these rules. Retain the checked entry work; replace the failed boundary application.

#### Summary
Complete SPEC_Call_fail_balance and SPEC_Call_fail_depth without statement changes. Use the validated result adapter for the charged prefix and the native refund helper for never-entered continuations. Remove the failed matching experiment and validate both proofs in the main theory.

#### Approach
Preserve the checked step-entry peeling. Replace SPEC_ALL/Q.INST matching with the validated result-variable adapter, then reduce the appropriate balance/depth branch and use call_refund_unuse_apply before the existing frame finish machinery. Handle depth's general value offset through premises, not a copied vo=1 specialization.

#### Not to try
Do not reconstruct access or gas internals in either consumer. Do not attempt further direct irule call_prefix_prog_apply against an alias-rich chosen RHS. No changes to frozen theorem statements or timeout configuration.

### C2.1.3: Expose and validate a result-variable prefix adapter
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: An equality transitivity corollary of the checked native equation removes all RHS matching constraints; remaining comparisons are explicit normalization obligations.
- Dependencies: C2.1.1
- Checkpoint: yes

#### Progress note
New boundary required by E0019; no existing proof is claimed for this output.

#### Summary
Add call_prefix_prog_apply_result as a local corollary. Its conclusion has an unconstrained result variable. Check application and discharge all premises at the existing balance charged-state subgoal before further consumer work.

#### Statement
Let H be exactly the antecedent of call_prefix_prog_apply and R its displayed native RHS (the continuation applied to the computed charged state). Prove locally: H /\ R = result ==> call_prefix_prog op cont s = result. Preserve every parameter and premise of H; result is a fresh variable of the RHS type.

#### Approach
Derive the adapter by stripping assumptions, applying call_prefix_prog_apply to H, and equality transitivity (a small metis_tac with that one theorem is acceptable). At the current balance equality use irule call_prefix_prog_apply_result without SPEC_ALL/Q.INST: only the LHS and result now participate in conclusion matching. Solve H using the existing aliases and stack bound; solve the separate R=result equality by targeted alias rewrites, numeral reduction, arithmetic associativity and record normalization. Use explicit witnesses for antecedent-only variables if necessary, rather than manual theorem instantiation.

#### Not to try
Do not add hypotheses to frozen SPEC statements. Do not unfold call_prefix_prog_def or access/meter internals. Do not retain failed FAIL_TAC placeholders in the completed adapter/application. If remaining premises fail, report the exact residual goal, not another No match experiment.

### C2.2: Successful entry and prepared CALL equation
- Kind: `proof`
- Risk: 2
- Work priority: 20
- Work units: 3
- Rationale: The checked prefix/result-variable adapter supplies the semantic equation. The review identifies a bounded local repair: establish the base execution bound while cost aliases are still named, then normalize that fact with the adapter premises. No new semantic invariant or definition is needed.
- Dependencies: C2.1.2, C2.1.3
- Checkpoint: yes
- Progress transition: `refinement`

#### Progress note
Retain the current SPEC_Call proof and stipend repair as source progress, but do not certify the rejected C2.2 closure. Recheck both outputs after repairing step_call_prepared. E0025 and the subsequent review identify the remaining local arithmetic/normalization issue; they are not proof certificates.

#### Summary
Preserve the frozen SPEC_Call and step_call_prepared statements. Keep the existing successful-entry proof and stipend repair. Repair the prepared consumer by deriving its base execution bound before expanding cost aliases. Rebuild and require step_call_prepared to check before claiming closure.

#### Description
This component owns the local arithmetic helper, if needed, as well as the prepared consumer repair. The helper is elementary infrastructure for this one proof, not a new semantic prerequisite. Preserve the validated prefix and result-variable adapter rather than reopening CALL semantics.

#### Statement
Prove the existing frozen statements of SPEC_Call and step_call_prepared in prog/vfmProgScript.sml without any hypothesis or conclusion changes.

#### Approach
At the start of the prepared proof, before fs/gvs expands aliases, use the gasCost equality and total bound to establish `g + (static_gas op + access_cost rb addr + vCost + dCost + mCost) <= p.gasLimit`. If needed, first prove a [local] lemma `!a b c d e f h n:num. a + (b + c + d + e + f + h) <= n ==> a + (b + c + d + e + f) <= n` by elementary arithmetic, and apply it by matching to named quantities; retain the resulting base bound through exactly the normalization used for adapter obligations. Apply the existing result-variable adapter with narrowly targeted rewrites, run `holbuild --max-heap 12000 -j8 build vfmProgTheory`, and if it still fails report every remaining goal and the checked boundary, not only the first goal.

#### Not to try
Do not repeatedly move and AC-normalize call_gas assumptions. Do not send expanded conditional cost expressions to ARITH_TAC, use global AC simplification, unfold semantic internals in the consumer, or replace the checked adapter. Do not change frozen statements, introduce proof-search fallbacks or raise tactic timeouts. Do not claim component closure merely because SPEC_Call checks: step_call_prepared must also check.

### C2.3: Precompile CALL composition and witnesses
- Kind: `proof`
- Risk: 2
- Work priority: 20
- Work units: 8
- Rationale: The file already decomposes precompile entry, metering and exact execution; repair their state-field compositions using the validated interfaces.
- Dependencies: C1, C2.2
- Checkpoint: yes

#### Summary
Validate and repair all declarations after step_call_prepared up to SPEC_Invalid_outermost. This includes proceed_call_precompile_success_meter, proceed_call_precompile_success, step_precompile_success_exact, SPEC_Call_precompile and witness_precompile_identity, plus all declarations in that interval. Keep every frozen statement unchanged.

#### Approach
Check the existing precompile metering/exact-execution equations in source order and compose them with step_call_prepared. Track the parent reservoir and spill separately from child execution gas; apply validated record-update and exception boundaries rather than distributing large definition sets through SPEC_Call_precompile. Rebuild all witness consumers in the covered interval.

### C3: Validate and repair remaining tail rules
- Kind: `proof`
- Risk: 2
- Work priority: 20
- Work units: 8
- Rationale: Existing proofs supply the rule structure; state-gas normalization is centralized in the prerequisite machinery.
- Required for completion: yes
- Dependencies: C1, C2
- Checkpoint: yes

#### Summary
Cover every declaration from SPEC_Invalid_outermost through EOF. In particular repair SPEC_Invalid_outermost, SPEC_Invalid_inner, SPEC_SelfDestruct_outermost and SPEC_SelfDestruct_inner as needed. Validate unchanged tail proofs as well as edited ones.

#### Approach
Use the inventory from C1.1 to check every tail declaration, not only named theorems. Apply the validated handler boundaries separately for outermost and inner contexts; in SELFDESTRUCT follow execution charge before creation-state charge and preserve the frozen beneficiary/rollback conditions. If more machinery is needed, return to C1 rather than improvising shared definitions inside a rule.

#### Not to try
Do not repair unrelated files or pre-state-gas call libraries. Do not silently strengthen SELFDESTRUCT hypotheses if a branch fails.

### C4: Whole-theory build, frozen-statement audit and clean commit
- Kind: `build_probe`
- Risk: 1
- Work priority: 30
- Work units: 3
- Rationale: Mechanical verification after all scoped proof obligations are discharged.
- Required for completion: yes
- Dependencies: C2, C3
- Checkpoint: yes

#### Summary
Build the entire vfmProgTheory and audit all task constraints. Compare every pre-existing theorem statement against the baseline and ensure no cheats or prohibited trust/search workarounds remain. Commit only prog/ changes and leave git status clean.

#### Approach
Run holbuild --max-heap 12000 -j8 build vfmProgTheory from the repository root with no tactic-timeout override, checking for parser warnings. If the tool wall-clock timeout interrupts a progressing build, rerun with a larger call timeout up to 3600 seconds. Audit statement identity, theorem-name preservation, file scope, prohibited constructs and temporary files; commit with the exact required Co-Authored-By and Bot trailer lines from TASK.

#### Not to try
Do not report a cheat-backed or partial checkpoint build as completion. Do not use Holmake, --no-cache, execution-spec tests, or stop processes by name.
