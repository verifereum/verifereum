# PLAN

## Structured Components

### C1: Validate shared state-gas proof machinery before repairing frozen rules
- Kind: `proof_group`
- Risk: 3
- Work priority: 0
- Work units: 0
- Rationale: Derived from child component C1.2 risk 3. Access and delegation segments validated, but full prefix composition and meter segment not validated; broad normalization times out and staged charge leaves nested monadic continuation requiring better boundary interface.
- Required for completion: yes

#### Summary
Build and validate reusable semantic interfaces before attempting any frozen rule. Preserve all existing theorem statements and semantics. Isolate access/delegation reduction and no-spill charge/refund arithmetic from separation-logic consumers.

#### Not to try
Do not begin frozen theorem proofs until all needed machinery is validated. Do not unfold bind, access_address and exception handling in a single broad gvs. Do not assume Abbrev equations rewrite ordinary field expressions.

#### Argument
Write B for static_gas op + access_cost rb addr + vCost + dCost + mCost and N for stateCost. The bound N ≤ sg makes charge_new_account reduce sg to sg-N without changing gasUsed or sp; hence the frozen call_gas input is correct despite the semantics charging creation before computing the grant. After both execution charges gasUsed is g+B+dynamicGas. On never-entry, refund returns MIN N sp to execution gas and the remainder to the reservoir, giving sg-N+(N-MIN N sp)=sg-MIN N sp. The final stipend subtraction matches the frozen postcondition. Access and delegate operations preserve accounts and context fields while producing precisely newRb/newDom. Package these facts before unfolding handle_step or separation assertions.

#### Definition design
Do not change definitions. Use the existing charge_new_account_apply, credit_new_account_apply, charge_state_gas_no_spill_apply and credit_state_gas_refund_apply interfaces after checking their exact signatures. New local boundary lemmas must expose concrete (INL result, updated-state) equations, with explicit contexts/rollback/msdomain equalities, not opaque abbreviation premises. A peeled CALL prefix must stop before the balance/depth decision and permit both outcomes; do not use successful-entry step_call_prepared as the only interface to failure rules.

#### Code structure
Keep all changes under prog/. Put new [local] semantic helpers before SPEC_Call_fail_balance in vfmProgScript.sml, adjacent to existing charge/access helpers or the CALL block. Validate helper proofs in a prog-only temporary theory or checkpoint that does not depend on the unfinished rules. Do not port vfmProgCallScript.sml or alter spec/. Retain existing public theorem names and statements.

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
- Rationale: The failed residual has known-success operations on an explicit nonempty context. Separate operation equations eliminate nested continuations before arithmetic normalization.
- Dependencies: C1.1
- Checkpoint: yes
- Progress transition: `refinement`

#### Progress note
E0002 supplies partial access/delegate and no-spill charge evidence, not a completed prefix proof. Retain that source and validate it with the new composition obligations.

#### Summary
Retain the build-clean access and delegate segments. Prove short meter operation equations before composing any bind spine. Normalize arithmetic only on scalar goals. Validate the complete reusable CALL prefix before touching frozen rules.

#### Approach
Build short scalar and primitive-operation boundaries first, then meter composition, then the actual access-plus-meter prefix. Existing successful helpers remain source prerequisites, not certification of new descendants.

#### Not to try
Do not run gvs with AC ADD_ASSOC ADD_COMM across nested bind cases. Do not unfold consume_gas/get_current_context globally through the remaining continuation. Do not compensate for RHS-only schematic parameters with long qspecl/ASSUME/MATCH_MP plumbing.

#### Argument
Under stateCost <= stateGasLeft the creation charge cannot spill into execution gas. The base execution charge therefore determines the gas_left supplied to call_gas; static checking and memory expansion preserve that meter. A successful dynamic charge and sender lookup finish the prefix. Each operation is evaluated on an explicit head context so the next bind reduces immediately, rather than exposing the entire continuation to rewriting.

#### Definition design
Use operation application equalities with s.contexts = (c,k)::cs as their interface. Conclusions must expose INL and the updated state, preserving rollback/domain fields. Conditional equations with parameters only in premises/RHS are elimination facts: establish their instantiated equation using irule and assumptions, then rewrite with that equation; do not expect simp to guess such parameters. No new semantic definitions or changed frozen statements.

#### Code structure
Validate helpers in prog/vfmProgCallPrefixProbeScript.sml. Keep definitions mirrored only for this independent probe; later integration must use the actual vfmProg boundary definitions. Mark helper theorems local. Do not edit frozen rule proofs during this subtree.

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

### C1.2.3: Validate access and meter composition against the CALL spine
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: Access/delegate effects are already evaluated; composition now uses their explicit state and the validated meter interface.
- Dependencies: C1.2.2
- Checkpoint: yes

#### Summary
Complete the originally required reusable CALL prefix boundary. Match the actual step_call order and expose the state at the balance/depth or child-entry branch. Recheck access/delegate equations and the no-spill meter together. Frozen rule proofs remain untouched until shared machinery validation is complete.

#### Approach
Read the actual step_call spine and peel only to the prefix boundary. For call_access_segment or call_delegate_segment, first derive the specific application equality via irule against the current state and delegate_check premise, then rewrite that equality; do not ask simp to infer newRb/newDom/cost. Apply call_meter_segment after access effects, preserving its rollback/domain result, and validate the prefix on the actual expression rather than only an invented stand-alone program.

#### Not to try
Do not duplicate delegation case analysis at every frozen consumer. Do not treat an independent probe build as a proof of the frozen SPEC rules, or silently alter call_gas ordering to ease composition.

### C1.3: Validate refund, exception and tail normalization interfaces
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 8
- Rationale: Refund arithmetic follows from MIN ≤ stateCost ≤ sg; existing record-update helpers provide the semantic operations.
- Dependencies: C1.1, C1.2
- Checkpoint: yes

#### Summary
Package the never-entered charge/refund calculation and abort outcomes. Validate exception/handler boundaries needed by inner and outermost rules. Validate precompile and SELFDESTRUCT shared normalization identified by the inventory before frozen proofs begin.

#### Statement
For N ≤ sg and c = MIN N sp, charging N then refunding N leaves stateGasLeft = sg-c, stateGasSpilled = sp-c, and gasUsed = G-c; abort then subtracts stipend under stipend ≤ G-c. Include local operational equations for the balance/depth abort continuations and exact preservation of unrelated state fields.

#### Approach
Use the existing charge/refund helpers and elementary natural arithmetic instead of unfolding them in consumers. Check handle_create_not_none and return_destination_case_const against the tail handler paths, and extract any missing local normalizations there. For precompile and SELFDESTRUCT reuse existing helper bodies where possible, isolating only new state-gas record calculations; checkpoint completion requires a checked build of all machinery used downstream.

#### Not to try
Do not cancel truncated subtraction without its bound. Do not assume refund restores sg when sp is positive. If a concrete probe contradicts a frozen rule, escalate for a counterexample gate rather than adjusting it.

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
