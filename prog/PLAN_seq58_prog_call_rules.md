# PLAN

## Structured Components

### C1: Validate shared state-gas proof machinery before repairing frozen rules
- Kind: `proof_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The frozen CALL hypotheses explicitly exclude a new spill; charging and refunding therefore have direct record-update proofs. The known obstruction is abbreviation normalization, not a missing semantic invariant.
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

### C1.2: Prove access/delegation and CALL prefix boundaries
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 8
- Rationale: Each segment is straight-line monadic evaluation with access_check hypotheses and explicit state fields.
- Dependencies: C1.1
- Checkpoint: yes

#### Summary
Prove a reusable access/delegate boundary with newRb/newDom outputs. Prove a CALL prefix equation through stack popping, access, execution charge, no-spill creation charge, memory expansion and dynamic gas charge. Leave the balance/depth continuation visible so the same equation serves all CALL outcomes.

#### Statement
New local outputs: (1) the address/delegate segment computes the code selected by get_delegate and the cost dCost, updating only rollback/msdomain as specified by delegate_check; (2) under the frozen operand, access, gas and no-spill premises, the prefix reaches a caller with stack DROP (6+vOff) ss, memory em, gasUsed g+B+dynamicGas and stateGasLeft sg-stateCost, leaving stateGasSpilled unchanged. The remainder is exactly the balance test and subsequent set_return_data/depth/proceed_call continuation of step_call_def.

#### Approach
Peel step_call_def in execution order using one bind at a time. Prove delegation by cases on get_delegate, normalize field equalities before applying access_address_split, and hide this expansion behind its boundary equation. Prove the prefix in short segments with explicit state equality interfaces; validate both value-offset cases and the charged/noncharged cases.

#### Not to try
Do not copy the long nested qpat_assum/manual theorem plumbing of the existing step_call_prepared proof. Do not add sender-balance or depth-success premises to the common prefix.

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
