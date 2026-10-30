# Frozen CALL-rule baseline and interface audit

Baseline: `48d421654525f06680177d4f5d64374cd56f6320:prog/vfmProgScript.sml`.
The immutable git object is the full statement/name inventory (including aliases).
No edits to that file have been made at this checkpoint. Later audit should
compare its diff against that object: only Proof/QED bodies and new local
helpers may differ; all original theorem declarations must remain.
`SPEC_Call_fail_balance` lines 4803-4852 matches the TASK statement.

## Tail declaration coverage (baseline line numbers)

- 4803-5086: SPEC_Call_fail_balance (the only cheat), SPEC_Call_fail_depth.
- 5087-5475: SPEC_Call, call_gas_cost_covers_stipend,
  call_stack_after_pop_has_room, call_static_check_success, step_call_prepared.
- 5476-5893: proceed_call_precompile_success_meter,
  proceed_call_precompile_success, handle_step_success_memory_exact,
  step_precompile_success_exact, repay_absorb_meter_fields,
  SPEC_Call_precompile, witness_precompile_identity.
- 5894-6538: revert_positive_spill_probe, SPEC_Return_outermost_counterexample,
  revert_positive_spill_side_conditions, SPEC_Return_outermost,
  inner_revert_spill_execution, SPEC_Return_inner_spill_counterexample,
  restored_unused_gas, restored_unused_gas_bound, restored_unused_gas_sub,
  SPEC_Return_inner. Existing counterexample lemmas concern earlier versions;
  the current Return statements already contain the corrected meters.
- 6539-6895: SPEC_Invalid_outermost, SPEC_Invalid_inner,
  SPEC_SelfDestruct_outermost, SPEC_SelfDestruct_inner.
- 6899-EOF: initial_state_contract, zero_value_call_def.

## Shared interfaces

Existing local helpers: charge_new_account_apply (1943),
credit_new_account_apply (1919) via credit_new_account_context_def (1902),
charge_state_gas_apply (1970), credit_state_gas_refund_apply (2166),
guarded_credit_state_gas_refund_apply (2179),
charge_state_gas_no_spill_apply (2192).
The charge requires a nonempty context and enough reservoir. Credit needs
only a nonempty context: it uses MIN with the *existing* spill, even when
the immediately preceding charge did not spill. Thus charge/refill is not
identity for positive pre-existing spill.

Independent validation: vfmProgCallMeterProbeTheory proves the symbolic
charge/refill composition for both flag values, and a numeric meter instance
with sg=183600, sp=7, gasUsed=200000 giving sg=183593, sp=0,
gasUsed=199993. It does not import unfinished vfmProgTheory.

CALL spine: pop/memory info; destination access; optional delegate access;
base execution charge; no-spill creation charge; static check; expansion;
grant computation/charge; balance decision; depth decision; continuation.
access_address_split needs access_check on the actual state's msdomain;
Abbrev markers in the SPEC harness must be exposed before applying it.
Delegation preserves accounts and contexts but updates rollback/msdomain.

Exception boundary: handle_create_not_none avoids irrelevant outputTo cases
for non-deposit exceptions. Invalid inner uses restore/forfeit and parent
absorb/repay. SELFDESTRUCT needs the same no-spill charge boundary and
successful absorb/repay normalization (not failure restoration).
Precompile helpers track exact child meters and exact parent absorb/repay;
keep those interfaces rather than unfold their implementation at SPEC level.
