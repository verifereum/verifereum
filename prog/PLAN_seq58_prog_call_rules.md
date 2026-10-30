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

### C1.3.2: Validate inventoried handler and tail boundaries independently
- Kind: `definition_probe`
- Risk: 2
- Work priority: 10
- Work units: 3
- Rationale: This is a bounded extraction/build and interface check of identified existing helpers, with escalation for missing semantic obligations rather than speculative handler proofs.
- Dependencies: C1.3.1
- Checkpoint: yes

#### Summary
Use the existing audit to validate the exact tail normalization interfaces before frozen proofs. Check non-deposit exception handling, precompile exact meters, and successful versus failing parent-meter reconciliation. Record exact checked signatures and uncovered boundaries at the checkpoint.

#### Description
Inventory anchors are prog/CALL_RULES_AUDIT_seq58.md lines 53-58 and the existing helpers proceed_call_precompile_success_meter, proceed_call_precompile_success, handle_step_success_memory_exact, step_precompile_success_exact, repay_absorb_meter_fields, restored_unused_gas, restored_unused_gas_bound and restored_unused_gas_sub. Locate handle_create_not_none and its actual defining theory before using it. Validate helper proofs/dependencies in an independent prog theory (or cite checked prerequisite-theory exports where applicable), without proving or changing frozen SPEC declarations. Explicitly check which interfaces the existing Invalid and SELFDESTRUCT proof bodies consume. Record missing boundaries and request refinement of C1.3 before declaring the machinery phase complete if any are absent.

#### Approach
Read the named helper signatures and the relevant tail proof bodies, then build a minimal independent validation theory containing only the necessary existing helper dependency closure. Map each tail family to its checked interfaces and distinguish successful absorb/repay from failure restore/forfeit; report exact residual goals if a helper fails instead of growing a generic simplifier.

#### Not to try
Do not repair the frozen SPEC proofs during this probe, duplicate the entire vfmProgScript.sml, or certify interfaces merely because their names appear in the inventory. Do not add unplanned replacement handler lemmas; escalate the precise missing boundary at this checkpoint.

### C2: Repair the frozen CALL family
- Kind: `proof_group`
- Risk: 2
- Work priority: 10
- Work units: 0
- Rationale: The shared prefix and outcome boundaries remove the repeated monadic reduction; remaining work is SPEC framing and existing continuations.
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

### C2.1: Balance and depth failure rules
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: Both branches are deterministic aborts after the same prefix and refund.
- Dependencies: C1
- Checkpoint: yes

#### Summary
Replace the only current cheat in SPEC_Call_fail_balance. Repair SPEC_Call_fail_depth with the same interfaces. Remove the obsolete attempted proof and debug-output code rather than leaving a misleading second implementation.

#### Statement
SPEC_Call_fail_balance and SPEC_Call_fail_depth, exactly as frozen.

#### Approach
After IMP_EVM_SPEC expose plain field equalities and apply the prefix. Use sender.balance < value for the first rule and the frozen context-count condition for the second, then apply the refund/abort boundary and frame normalization. Audit each postcondition component, especially creditBack and returnData.

### C2.2: Successful entry and prepared CALL equation
- Kind: `proof`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: The successful continuation is exactly the remainder exposed by the validated prefix.
- Dependencies: C1, C2.1
- Checkpoint: yes

#### Summary
Repair SPEC_Call and step_call_prepared without changing their statements. Validate every intervening helper declaration, including call_gas_cost_covers_stipend, call_stack_after_pop_has_room and call_static_check_success. Reuse the common prefix instead of duplicating its expansion.

#### Statement
Frozen SPEC_Call and step_call_prepared and all intervening declarations through step_call_prepared.

#### Approach
Use balance sufficiency and LENGTH cs < 1024 to select proceed_call after the prefix. For step_call_prepared derive the base execution-cost bound from g+gasCost ≤ gasLimit and expose exactly its frozen updated-state argument; for SPEC_Call finish the existing separation-logic entry/frame argument.

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
