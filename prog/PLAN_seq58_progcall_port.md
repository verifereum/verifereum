# PLAN

## Structured Components

### C1: Complete the CALL port under the explicitly amended contract
- Kind: `proof_group`
- Risk: 3
- Work priority: 0
- Work units: 0
- Rationale: Derived from child component C1.3.6 risk 3. Nested entry scalar/list boundaries are checked, but full step_call/step_create and precompile execution need compositional meter/safety interfaces not supplied by preceding components. proceed_call dispatches precompiles immediately after push; its general budget contract therefore requires precompile preservation before step_call, not only later all-opcode work.
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
- Risk: 3
- Work priority: 20
- Work units: 0
- Rationale: Derived from child component C1.3.6 risk 3. Nested entry scalar/list boundaries are checked, but full step_call/step_create and precompile execution need compositional meter/safety interfaces not supplied by preceding components. proceed_call dispatches precompiles immediately after push; its general budget contract therefore requires precompile preservation before step_call, not only later all-opcode work.
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

### C1.3.6: Compositional CALL/CREATE entry preservation
- Kind: `proof_group`
- Risk: 2
- Work priority: 6
- Work units: 0
- Rationale: Separate all-result monadic composition, neutral operations, immediate precompile execution, and grant accounting. Each is finite semantic decomposition using checked meter and rooted-budget boundaries.
- Progress transition: `refinement`

#### Progress note
E0017 remains partial evidence only; no whole-entry proof continuity claimed.

#### Summary
Preserve the checked shape and push facts. Introduce a reusable contract that tracks error states as well as success. Prove precompile dispatch before general proceed_call. Assemble CALL and CREATE without changing exported hypotheses.

#### Not to try
Do not unfold whole step_call/proceed_call/precompile bodies together. Do not use unrestricted old call_exn_safe_step_call. Do not claim arbitrary-address dispatch is safe: dispatch_precompiles ends in fail Impossible outside its domain.

#### Argument
Meter-neutral prefixes and primitive meter contracts preserve backing and claim on every result. A successful grant payment reserves the child's full claim against the original pre-grant context; child push is justified by call_meter_entry_budget, not by comparing with the depleted intermediate parent. Immediate precompile execution only spends that child claim. Abort paths refund only a backed grant margin, including the value stipend paid from the opcode cost.

#### Definition design
Use a result-indexed contract call_meter_safe P m Q defined by !s r t. P s /\ m s = (r,t) ==> Q r t /\ (!e. r = INR e ==> e <> SOME Impossible /\ e <> SOME Unimplemented). Prove bind with an intermediate success predicate R x and an explicit error-post implication; never infer a meter property on error from a success-only triple. Keep call_meter_result as the fixed-tail primitive boundary, and use rooted call_meter_budget at pushes. Test bind on consume followed by refund and on an early failure before using it across opcode spines.

#### Code structure
Keep bounded entry facts in prog/vfmCallEntryScript.sml. Put generic composition and primitive adapters in a new prog theory below entry integration; put precompile preservation in a separate prog theory depending on those adapters. Integrate whole opcode contracts in a new entry-step theory if adding imports to vfmCallEntry would make a cycle. Do not copy the production local safety library wholesale.

### C1.3.6.1: Retain and audit bounded entry boundaries
- Kind: `boundary_lemma`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: The six boundaries are already checked in E0017; this leaf audits their bounded scope and commits them.
- Dependencies: C1.3.4, C1.3.5
- Progress transition: `refinement`
- Carries progress/evidence from: E0017

#### Progress note
Reuses partial source evidence, not automatic certification of a new leaf.

#### Summary
Retain proceed_create and nonprecompile proceed_call shapes. Retain the original-frame budget push and its two proceed corollaries. Check and commit the theory without implying whole-opcode closure.

#### Statement
Outputs: call_meter_proceed_create_shape, call_meter_proceed_call_shape, call_meter_entry_budget, call_meter_proceed_create_budget, call_meter_proceed_call_budget as currently in vfmCallEntryScript.sml.

#### Approach
Build vfmCallEntryTheory and inspect the nonprecompile premise and pre-grant comparison. Commit the stable partial file with required trailers.

### C1.3.6.2: All-result contract and composition probes
- Kind: `definition_probe`
- Risk: 2
- Work priority: 1
- Work units: 3
- Rationale: Contract laws follow by splitting monadic result pairs; small primitive probes test the error boundary.
- Dependencies: C1.3.5
- Checkpoint: yes

#### Summary
Define result-indexed safe contracts. Prove return, allowed fail, consequence, bind and ignore-bind laws. Probe error-state propagation and successful grant restoration.

#### Statement
Bind interface: safe P g (\r s. case r of INL x => R x s | INR e => Q (INR e) s) /\ (!x. safe (R x) (f x) Q) ==> safe P (bind g f) Q. Include invariant specialization and conversion from primitive call_meter_result contracts with separately proved exception exclusions.

#### Approach
Case split g s and its sum result once in the library. Validate consumers on consume_gas followed by return, early fail OutOfGas, and call_meter_return_grant under its existing grant premise.

#### Not to try
Do not bake exact stack length or exact rollback into the generic contract; these belong in instantiated predicates. A meter result alone does not exclude Impossible.

### C1.3.6.3: Neutral-operation and primitive safe adapters
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 2
- Work units: 8
- Rationale: Finite reader/updater computations and already proved primitive meter laws, with exception exclusions checked separately.
- Dependencies: C1.3.6.2

#### Summary
Supply compositional adapters needed by CALL, CREATE and precompiles. Cover readers, stack, memory, access and non-meter context updates. Combine primitive meter laws with their actual error exclusions.

#### Statement
For the operations occurring in step_call, step_create and precompile bodies, prove fixed-tail call_meter_result preservation under nonempty backed gas-bounded input, together with forbidden-error exclusion where valid. Grant-consuming and grant-refunding operations retain their stronger margin premises rather than receiving an unrestricted adapter.

#### Approach
Prove a neutral lifting boundary from preservation of contexts tail and top gasLimit/gasUsed/stateGasSpilled/stateGasCommitted to call_meter_result; other fields may change. Instantiate for readers, stack/memory/access/account operations, allowed assertions and terminal finish/revert; wrap existing vfmCallMeter results rather than unfolding meter arithmetic in each consumer.

#### Not to try
Do not duplicate 1500 lines of safety-only helpers or assert that arbitrary set_current_context preserves meters.

### C1.3.6.4: Immediate precompile preservation
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 3
- Work units: 8
- Rationale: Finite address dispatch and spend-only computations; cryptographic functions are opaque and their return cases suffice.
- Dependencies: C1.3.6.3
- Checkpoint: yes

#### Summary
Prove a safe fixed-tail meter contract for each dispatched precompile. Combine under membership in precompile_addresses. Lift to rooted budget so the theorem can follow child push.

#### Statement
s.contexts = (c,rb)::rest /\ call_meter_backed c /\ c.gasUsed <= c.msgParams.gasLimit /\ fIN addr precompile_addresses /\ dispatch_precompiles addr s = (r,t) ==> call_meter_result c rb rest t /\ (!e. r = INR e ==> e <> SOME Impossible /\ e <> SOME Unimplemented). Also provide its call_meter_budget corollary via call_meter_result_budget.

#### Approach
Inspect each precompile body and prove a separate contract using composition, consume_gas, return-data updates, allowed failures and finish. Split pure cryptographic result cases without evaluating algorithms; then unfold only dispatch_precompiles and the finite address set to exclude its Impossible default.

#### Not to try
Never drop the address-membership premise. Do not expand all precompile bodies in a single dispatch proof.

### C1.3.6.5: Compose reserved-budget CALL and CREATE entry
- Kind: `proof_group`
- Risk: 2
- Work priority: 50
- Work units: 0
- Rationale: A single reserved-claim invariant retains exactly the paid stipend and grant information lost by ordinary result adapters. Existing scalar and entry boundaries discharge its arithmetic.
- Progress transition: `refinement`
- Carries progress/evidence from: E0023

#### Progress note
E0023 checked proceed_call including immediate precompiles and four margin lemmas. Retain their proofs unchanged; the whole opcode obligations remain unfinished and no continuity certificate is requested for new outputs.

#### Summary
Retain the checked proceed_call and scalar margin boundaries. Introduce a fixed-tail reservation predicate tracking both backing surplus and claim credit. Transport this predicate through neutral operations and credit before releasing it at abort or child entry. Assemble CALL and CREATE as separate consumers, with errors included and no new exported premises.

#### Not to try
Do not infer reservation preservation from call_meter_result: it has forgotten the surplus. Do not unfold whole opcodes and all neutral operations together. Do not add backing premises to exported rules or change spec files.

#### Argument
For an anchor context c, a reservation k in current context d means spilled(d)+committed(d)+k <= used(d), gas-boundedness, and claim(d)+k <= claim(c), with the same rollback and tail. Paying the opcode cost establishes a stipend reservation. State charging preserves it. The call_gas margin lemma changes that reservation into the actual grant after payment, since its claim bound spends at most the already reserved stipend. Refund consumes the grant reservation; child entry spends it on the new child. All early errors can forget the reservation and retain ordinary budget. CREATE has no stipend: its withholding boundary directly establishes its grant reservation.

#### Definition design
Define call_meter_reserved c k rb rest s by an existential current d, fixed contexts, gas bound, backing surplus >= k, and claim d+k <= claim c. Keep the anchor c fixed across composition. Define a success-reserved post only as a convenience: INL results carry a possibly value-dependent reservation and INR results carry call_meter_result c rb rest. First test zero reservation, weakening, neutral transport, charge/credit and grant payment; do not add reservoir or account restrictions. Readers must retain returned values as well as the reservation.

#### Code structure
Keep checked EntryStep lemmas in place. Put the reservation definition and reusable adapters in a new prog/vfmCallReserveScript.sml importing EntryStep and Ops; put whole entry assembly in a downstream prog theory to avoid circular imports. Use named semantic suffix lemmas for grant/abort/entry rather than an ML tactic library that unfolds neutral definitions in every consumer.

### C1.3.6.5.1: Reservation interface and transport laws
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: These are existential fixed-tail wrappers around checked margin arithmetic and neutral field equalities.
- Checkpoint: yes

#### Summary
Define the fixed-anchor reserved predicate. Prove zero, forgetting and neutral transport laws. Supply value-retaining readers and reservation-preserving neutral, charge and credit adapters. Check the abstraction before opcode assembly.

#### Statement
call_meter_reserved c k rb rest s <=> ?d. s.contexts = (d,rb)::rest /\ d.gasUsed <= d.msgParams.gasLimit /\ d.stateGasSpilled + d.stateGasCommitted + k <= d.gasUsed /\ call_meter_claim d + k <= call_meter_claim c. Outputs: reserved at k=0 iff call_meter_result; reserved implies ordinary result; neutral fixed-tail transport; reservation-preserving safe adapters for assert_not_static, expand_memory, set_return_data, push_stack, inc_pc, access_address and ensure_storage_in_domain; readers get_gas_left/get_callee/get_num_contexts retaining values; charge_new_account and credit_new_account preserving reservation on all results and excluding forbidden errors.

#### Approach
Prove neutral transport once from call_meter_neutral_def, then establish relational neutral boundaries for the listed primitives by their small definitions, reusing existing safety proofs for error exclusion. Lift charge_margin and credit_margin through the existential current context, retaining the fixed anchor claim inequality; reader adapters must expose the current context when arithmetic needs it.

#### Not to try
Do not duplicate long concrete context records at use sites. Do not require successful results for neutral preservation: stack overflow or write protection still leave the meter neutral.

### C1.3.6.5.2: Reservation acquisition and discharge at grant boundaries
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 5
- Rationale: Checked consume/call_gas margins and entry budgets give the scalar steps; aborts consist of neutral operations plus one grant refund.
- Dependencies: C1.3.6.5.1

#### Summary
Acquire a stipend reservation on successful opcode payment. Convert it into a child grant reservation after call_gas and consume_gas. Release reservations on abort or spend them on child entry. Include CREATE withholding and the no-refund collision branch.

#### Statement
Provide success/error-sensitive consume adapters: from reserved c 0 and margin <= cost, successful consume_gas cost yields reserved c margin, and failure yields ordinary result. Provide a CALL grant-payment adapter from reserved c margin with (if value=0 then 0 else call_stipend)<=margin, computing call_gas with zero cost arguments and returning reserved c grant after payment. Provide reserved c grant -> ordinary-result safety for abort_call_value grant and abort_unuse grant; reserved c grant -> rooted-budget safety for proceed_call and proceed_create with the original anchor budget. Lift withhold_create_gas to return reserved c grant on success. Provide ordinary-result safety for abort_create and abort_create_exists.

#### Approach
Use the checked scalar lemmas to establish reservation changes, and expose these as call_meter_safe contracts so bind composition does not manually track records. Refund uses surplus >= grant to justify natural subtraction and claim increase by grant; compose neutral push/return-data/pc operations around it, forgetting reservation on failures before refund. For CREATE collision, forget the withheld reservation rather than refunding it: the semantics leaves that grant paid.

#### Not to try
Do not assert an abort always refunds: push_stack can fail before the refund. Ordinary result on that error is sufficient. Do not use CREATE's ordinary withholding adapter if it discards the returned grant or its surplus.

### C1.3.6.5.3: Assemble whole step_call budget and safety
- Kind: `proof`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: All meter-changing segments now have reservation contracts; remaining structure is finite monadic branching.
- Dependencies: C1.3.6.5.2
- Checkpoint: yes

#### Summary
Prove step_call preserves the existing rooted budget on all results. Exclude Impossible and Unimplemented. Keep immediate precompile execution behind the checked proceed_call boundary. No caller-facing assumptions are introduced.

#### Statement
Under the existing rooted-budget and nonempty protected-prefix entry premises, step_call op s = (r,t) implies call_meter_budget n ceiling t and (!e. r = INR e ==> e <> SOME Impossible /\ e <> SOME Unimplemented). Use the same internal premises as the original whole-entry obligation.

#### Approach
Peel step_call only to primitive boundaries and compose via call_meter_safe_bind. Ordinary prefix operations preserve zero reservation; successful opcode consumption reserves (if value=0 then 0 else call_stipend), justified by the positive-value cost and constants. Charge, static check and memory expansion preserve it; grant payment converts it to grant, then credit/abort or proceed spends it. Lift ordinary early-error results back to the anchor rooted budget.

#### Not to try
Do not reopen dispatch_precompiles or unfold neutral primitives in this proof. Do not assume call_has_value op: the semantics' valueOffset already determines zero value on other operations.

### C1.3.6.5.4: Assemble whole step_create budget and safety
- Kind: `proof`
- Risk: 2
- Work priority: 40
- Work units: 5
- Rationale: CREATE has no stipend subsidy; withholding establishes the grant directly, and each branch is covered by the preceding boundaries.
- Dependencies: C1.3.6.5.2
- Checkpoint: yes

#### Summary
Prove step_create preserves rooted budget and excludes forbidden errors on all results. Handle early abort before charging and collision after withholding separately. Use the existing proceed_create entry boundary. Build the entry theory and its consumers without changing exports.

#### Statement
Under the existing rooted-budget and nonempty protected-prefix entry premises, step_create two s = (r,t) implies call_meter_budget n ceiling t and (!e. r = INR e ==> e <> SOME Impossible /\ e <> SOME Unimplemented).

#### Approach
Compose the zero-reservation prefix using ordinary adapters, including code-size/static/domain checks and memory read. The insufficient-balance/nonce/depth branch uses abort_create without grant accounting; the other branch charges then withholds, exposing the grant reservation. Collision forgets it and uses abort_create_exists; successful entry spends it through proceed_create_budget. Build the new assembly theory and downstream target with normal checkpoint resumption.

#### Not to try
Do not import CALL stipend reasoning into CREATE or refund its collision grant. No whole-semantics simplifier expansion and no timeout overrides.

### C1.3.7: Complete inner execution meter coverage
- Kind: `proof_group`
- Risk: 2
- Work priority: 50
- Work units: 0
- Rationale: Existing checked compositions validate the fixed-tail interface; remaining work separates neutral updates, state-meter effects, and finite dispatch.
- Progress transition: `refinement`
- Carries progress/evidence from: E0033

#### Progress note
E0033 supplies checked partial helpers, not a proof of full dispatch or any new child obligation. Retain those helpers unchanged; no continuity certification is requested.

#### Summary
Preserve the checked arithmetic, context-reader, exponentiation and memory helpers in vfmCallInner. Complete remaining ordinary instructions with fixed-tail call_meter_result contracts. Separate saved-context updates from state-charge/refund operations. Assemble step_inst with the already checked CALL/CREATE budget contracts, then lift to inner execution.

#### Not to try
Do not give CALL/CREATE a fixed-tail ordinary-result postcondition. Do not use arbitrary set_current_context as invariant-preserving. Do not unfold meter internals in final dispatch or use a single large all-opcode proof search.

#### Argument
Ordinary instructions preserve call_meter_result c rb rest on every result, including exceptional results. Its fixed-tail abstraction permits sequential composition without reopening budget arithmetic. CALL/CREATE can extend the context stack and therefore use the existing budget-level entry contracts instead. At dispatch, lift ordinary results to the anchored budget using call_meter_safe_anchor_budget; combine that with entry cases, then account for the fetch/PC plumbing of inner execution.

#### Definition design
Keep call_meter_safe and call_meter_result unchanged. Reader boundaries used with saved contexts must retain the returned value's equality to the current head; an invariant-only reader loses information required for safe record replacement. Every state-gas operation must have an all-result interface before storage or terminal dispatch uses it. No new hypotheses on exported rules are authorized.

#### Code structure
Keep additions in prog/vfmCallInnerScript.sml, after the existing checked helpers and before final dispatch. Family helpers are independently timed theorems. Retain existing source proofs; avoid unrelated cleanup or changes below prog/. A shared combinator is warranted only where it removes repeated semantic sequencing, not merely nested tactic syntax.

### C1.3.7.1: Neutral context, stack and control-flow family
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: These operations change only non-meter fields; saved-context provenance is the essential boundary.

#### Summary
Add a value-sensitive current-context reader boundary. Cover Pop, Push, Dup, Swap, DupN, SwapN, Exchange, Jump, JumpI, and inc_pc_or_jump. Include assertions and invalid-jump failures on all-result paths.

#### Statement
For each ordinary operation m in this family prove call_meter_safe (call_meter_result c rb rest) m (\r t. call_meter_result c rb rest t). Reader boundary: call_meter_safe (call_meter_result c rb rest) get_current_context (\r t. ?ctx. r = INL ctx /\ ctx = FST (HD t.contexts) /\ call_meter_result c rb rest t).

#### Approach
Prove the reader boundary directly from get_current_context, then retain its equality through the local context-update sequence using call_meter_safe_bind. Alternatively prove a dedicated neutral projection lemma for a complete saved-context operation; updates must preserve all meter fields and the message gas limit, not merely gasUsed.

#### Not to try
The existing current_inv theorem deliberately forgets the read value; it cannot justify writing back an arbitrary saved context. Never assert an unconditional invariant for set_current_context.

### C1.3.7.2: Remaining read, memory, copy and log operations
- Kind: `proof`
- Risk: 2
- Work priority: 20
- Work units: 8
- Rationale: Composition uses the checked memory/spend and result-lift interfaces and neutral state effects.
- Dependencies: C1.3.7.1

#### Summary
Retain existing keccak256/mload/mstore proofs and adapters. Cover Balance, SelfBalance, call-data load, all copy variants including MCOPY and external/return-data copies, external-code size/hash, BlockHash, BlobHash and Log. Cover remaining pure environmental reader instances through existing context/transaction helpers.

#### Statement
For each ordinary operation m in this family, prove call_meter_safe (call_meter_result c rb rest) m (\r t. call_meter_result c rb rest t). Parameterized copy helpers must state the reader contract actually required by their optional source reader.

#### Approach
Follow each definition's monadic sequence, reusing consume_inv, memory_info_inv, expand_inv, read_memory_inv and write_inv. If adding another copy repeats the same expansion/spend/read sequence, extract a parameterized sequencing helper with an explicit invariant-preserving continuation, and use it for new consumers; refactoring already checked keccak/mload is optional and only if directly useful.

#### Not to try
Do not expand all memory and account definitions at every use site. Domain-check failures must remain covered rather than assuming successful access.

### C1.3.7.3: Storage charge and refund family
- Kind: `proof`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: Storage's non-neutral effects are precisely charge/refund meter transitions; the surrounding account operations are meter-neutral.
- Dependencies: C1.3.7.1
- Checkpoint: yes

#### Summary
Prove SLoad/TLoad and SStore/TStore all-result interfaces. Give step_sstore_gas_consumption its own checked theorem. Expose any missing charge_state_gas and credit_state_gas_refund adapters as local family outputs before composing storage.

#### Statement
call_meter_safe (call_meter_result c rb rest) (step_sstore_gas_consumption address key value) (\r t. call_meter_result c rb rest t); analogous contracts for step_sload transient and step_sstore transient. Required local primitive adapters have the same pre/post shape for charge_state_gas amount and credit_state_gas_refund amount.

#### Approach
Follow the explicit storage sequence: stipend assertion, reads/access, refund-counter update, optional state refund, execution spend, state charge. Use checked primitive interfaces where available; prove missing invariant adapters by result-lift from the existing meter transition layer, then compose without unfolding its arithmetic in the storage theorem.

#### Not to try
Do not discard the state after an OutOfGas branch or assume a successful state charge. The stipend sentry constrains execution gas, not execution plus reservoir.

### C1.3.7.4: Terminal and selfdestruct operations
- Kind: `proof`
- Risk: 2
- Work priority: 40
- Work units: 5
- Rationale: Terminal results remain within the current frame until exception handling; meter effects need explicit interfaces, not a success-only argument.
- Dependencies: C1.3.7.2, C1.3.7.3
- Checkpoint: yes

#### Summary
Cover Stop, Return, Revert, Invalid and SelfDestruct. Prove finish and step_return success-flag interfaces where needed. Isolate selfdestruct's charge/refund and account-update tail before composing its full instruction.

#### Statement
For each operation in this family prove call_meter_safe (call_meter_result c rb rest) m (\r t. call_meter_result c rb rest t), covering both flags of step_return and every terminal exception result.

#### Approach
Inspect each terminal definition and prove its all-result contract before dispatch. Separate selfdestruct's meter-changing primitives from account/state updates; reuse storage-family charge/refund adapters when applicable and prove any additional primitive adapter locally with the existing transition layer.

#### Not to try
Do not conflate a terminal INR result with frame popping: frame merging belongs to the outer handler, not this instruction family. Do not infer all-result safety from success-only preservation.

### C1.3.7.5: Assemble opcode dispatch and inner execution
- Kind: `proof`
- Risk: 2
- Work priority: 50
- Work units: 5
- Rationale: Finite constructor dispatch after family contracts; entry branches already have budget-level proofs.
- Dependencies: C1.3.7.1, C1.3.7.2, C1.3.7.3, C1.3.7.4
- Checkpoint: yes

#### Summary
Complete step_inst coverage for every constructor in step_inst_def. Use existing Steps entry contracts for CALL and CREATE and ordinary-result lifting for other constructors. Prove the inner-execution budget and forbidden-exception contract required by the parent strategy, and check vfmCallInnerTheory.

#### Statement
All-result preservation of call_meter_budget n ceiling through step_inst and inner execution under the existing entry contracts' wf_state, budget and active-depth assumptions; INR results exclude SOME Impossible and SOME Unimplemented. Match the current parent consumer's exact inner-execution interface, without introducing new exported-rule hypotheses.

#### Approach
Read the current inner-execution definition and the checked Steps theorem signatures before stating this boundary. Case-split instruction constructors, lift ordinary family contracts with call_meter_safe_anchor_budget, and use the checked CALL/CREATE contracts directly; then compose instruction fetch and inc_pc_or_jump with the correct value-sensitive boundary. Audit every step_inst_def constructor, including JumpDest's consume_gas and pure environmental instances, rather than leaving implicit residual coverage.

#### Not to try
Do not force stack-extending entry branches through call_meter_result. Do not mix exception-handler unwind proofs into inner execution. If the consumer interface requires an assumption not implied at its existing call sites, escalate rather than weaken the frozen rule.

### C1.3.8: Prove deposit and exception-handler budget preservation
- Kind: `proof_group`
- Risk: 2
- Work priority: 50
- Work units: 0
- Rationale: The list-budget interface already matches. Scalar settlement can be proved over an arbitrary merged context before substituting the large semantic record.
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0040, E0041

#### Progress note
E0040 deposit work remains useful source evidence; E0041 identifies the missing abstraction, not a mathematical obstruction. No completed handler proof is claimed.

#### Summary
Retain the checked handle_create invariant proof. Separate scalar settlement from semantic pop matching. Complete internal/root pop and exception-handler preservation without expanding merged records in consumers.

#### Not to try
Do not simplify an abbreviation containing repeated absorb_state_gas records together with backed/claim definitions. Do not impose backing on the external caller.

#### Argument
Parent margin bounds the child's entire refundable claim. Absorption followed by repayment or failure credit preserves the sum of parent and child claims and yields a backed internal parent. Root exit instead uses the budget exit rule and does not require backing of the external caller.

#### Definition design
Use a named settlement function with a generic merged-context argument. Its backing and claim interfaces must hide logs and refund updates. Prove projection facts on an arbitrary context before substituting absorb_state_gas expressions; consumers must not normalize full records.

#### Code structure
Put scalar settlement helpers in prog/vfmCallMeterProbeScript.sml beside the existing pop lemmas. Put semantic pop and handler proofs in prog/vfmCallInnerScript.sml; retain the checked deposit helper chain.

### C1.3.8.1: Compact scalar settlement interface
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: Credit and repayment subtract the same bounded amount from gasUsed and spilled; projection-first arithmetic avoids record normalization blowup.

#### Summary
Introduce a compact settlement expression parameterized by success, credit, logs, and refund increments. Prove backing and claim preservation for an arbitrary merged context. Derive pop-shaped backed and claim-sum corollaries for the exact semantic expression.

#### Statement
Define settle success credit logs ar sr m to be repay_state_gas_spill_context (m with <|logs := logs; addRefund := ar; subRefund := sr|>) on success, and m with <|gasUsed := m.gasUsed - MIN credit m.stateGasSpilled; stateGasSpilled := m.stateGasSpilled - MIN credit m.stateGasSpilled; stateGasLeft := m.stateGasLeft + (credit - MIN credit m.stateGasSpilled)|> otherwise. Prove separately: call_meter_backed m ==> call_meter_backed (settle success credit logs ar sr m); call_meter_backed m /\ m.gasUsed <= m.msgParams.gasLimit ==> call_meter_claim (settle success credit logs ar sr m) = call_meter_claim m. Derive separate backing and claim equality corollaries when m = absorb_state_gas (parent with gasUsed := parent.gasUsed - (child.msgParams.gasLimit - child.gasUsed)) child.stateGasLeft child.stateGasSpilled child.stateGasCommitted, assuming parent.gasUsed <= parent.msgParams.gasLimit and parent.stateGasSpilled + parent.stateGasCommitted + call_meter_claim child <= parent.gasUsed. Claim equality is call_meter_claim (settle ... m) = call_meter_claim parent + call_meter_claim child.

#### Approach
First prove the scalar-field projections of settle over a variable m, splitting success and MIN only there; backing and claim then reduce to small natural arithmetic. Separately prove backing, gasUsed upper bound, and claim-sum for absorption under the parent margin by projection rewriting, then compose the generic settlement contracts. Test the corollaries with the actual logs/refunds/creation-credit arguments from call_meter_pop_pair, using only definitional rewriting to identify settle.

#### Not to try
Do not substitute the full merged record before proving the generic settle contracts. Do not use unrestricted simp to discover record equality; fold/unfold only the named settlement boundary.

### C1.3.8.2: Complete semantic pop and exception-handler budget boundary
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: Settlement contracts remove the observed bottleneck; internal pop uses the existing budget_pop interface and root exit uses budget_root_exit.
- Dependencies: C1.3.8.1
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0040, E0041

#### Progress note
Retains the original unfinished handler obligations and checked deposit helper source; neither previous episode certifies this leaf.

#### Summary
Finish handle_create budget lifting and both pop boundaries. Supply restore/forfeit and output contracts needed by handle_exception. Compose exception-handler preservation and exclusion of forbidden exceptions, retaining the original hypotheses.

#### Approach
Use parent_margin and call_meter_pop_pair, rewriting its settlement expression to the named settle function before budget_pop; discharge backed and claim premises directly with the new corollaries. Handle root exit with call_meter_budget_root_exit, not internal parent backing. Lift the existing fixed-tail handle_create invariant, use restore/forfeit claim interfaces and output-preservation contracts, and compose the exception handler with the existing step-inner boundary; build vfmCallInnerTheory.

#### Not to try
Consumers must not unfold absorb_state_gas, repayment, backed, and claim together on semantic records. Do not add an external-caller backing hypothesis or a callee-code assumption.

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
