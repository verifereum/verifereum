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

## Independent tail validation (2026-10-30)

`vfmProgCallTailProbeTheory` copies only the inventoried semantic helpers,
without importing `vfmProgTheory`. Its checked build validates:

- `handle_create_not_none`: `e <> NONE /\ s.contexts <> []` suffices for
  `handle_create e s = reraise e s`. This is a local helper in
  `prog/vfmProgScript.sml:4783`, not a prerequisite-theory export.
- `proceed_call_precompile_success_meter` and its public weaker projection:
  the fresh child inherits the parent's reservoir and baseline, has zero
  spill/commit, while the suspended parent reservoir becomes zero. Exact
  dispatch behavior supplies child execution usage and return bytes.
  The copied proof needed `get_accounts_def` added to its first rewrite set;
  the source helper currently omits it and is not yet validated in situ.
- `handle_step_success_memory_exact`: successful Memory output returns to
  `repay_state_gas_spill_context (absorb_state_gas
  (parent with gasUsed := parent.gasUsed-(childLimit-childUsed))
  childReservoir childSpill childCommit)`, with exact memory, stack, PC,
  return-data and log updates. Requires unused child gas <= parent usage,
  stack room, and zero child add/sub refunds.
- `repay_absorb_meter_fields`: successful merge refunds
  `MIN (parentReservoir+childReservoir) (parentSpill+childSpill)` execution
  gas and removes that same quantity from the merged reservoir/spill;
  baseline is preserved and commitment added.
- `restored_unused_gas`, `_bound`, `_sub`: restored unused gas includes
  `MIN sp used`, given used <= limit; parent subtraction is exact.

Remaining interface coverage questions (do not certify the machinery phase
complete merely from the preceding helper build):

- `step_precompile_success_exact` depends directly on frozen
  `step_call_prepared` (lines 5674-5677). Validating its current proof in
  isolation would require importing/re-proving that frozen obligation, which
  is prohibited until the machinery phase completes. Its semantic
  prerequisites above are checked; its full composition must be assigned
  explicitly to the later frozen-family phase or otherwise replanned.
- Invalid outermost/inner proof bodies use implementation reductions of
  `restore_state_gas`, `forfeit_remaining_gas`, `handle_exception`, and
  `pop_and_incorporate_context`; the inner branch then uses
  `credit_new_account_context (absorb_state_gas caller baseline 0 commit)`.
  No inventoried independent operational boundary covers these entire
  failure-handler updates. `restored_unused_gas` is arithmetic only.
- SELFDESTRUCT outermost/inner bodies use `access_address_split`,
  `charge_new_account_apply`/`charge_state_gas_apply` and direct reductions
  of `step_self_destruct` and successful handlers. Inner successful merge
  uses repay/absorb, not failure restore/forfeit. The checked Memory-output
  handler assumes zero child refunds; SELFDESTRUCT permits arbitrary refunds
  and Code output as well, so it is not a complete boundary for that family.

### Checked Invalid settlement boundary

`vfmProgCallTailProbeTheory` now independently checks
`handle_step_invalid_outermost_exact` and `handle_step_invalid_inner_exact`.
Both require the restored child execution-meter bound
`c.gasUsed - c.stateGasSpilled <= c.msgParams.gasLimit`.
This follows by natural subtraction from `wf_context`'s
`c.gasUsed <= c.msgParams.gasLimit`
(`spec/prop/vfmExecutionPropScript.sml:118-121`); consumers must extract that
existing well-formedness fact, not add a frozen SPEC hypothesis.
The inner boundary needs only parent stack room, not a parent gas bound.
It absorbs the child's baseline and commitment, credits the account charge,
restores rollback, pushes zero and clears return data for either destination.
The outer boundary retains commitment and resets spill and refunds.
The probe copies `credit_new_account_context_def` unchanged from vfmProg;
it does not import the unfinished SPEC theory. Both proofs bypass deposit
with `handle_create_not_none`, and normalize forfeiture arithmetic before
settlement. Checked build: tool output TO_seq58_prog_call_rules-20261030T133624Z_m0311_t001.

### Checked general successful settlement

The independent probe also proves `handle_exception_success_outermost_exact`,
`handle_exception_success_memory_exact` and
`handle_exception_success_code_exact` for arbitrary child add/sub refunds.
The inner boundaries require parent stack room and enough parent used gas to
return the child's unused grant. They repay spill after absorbing the child
meter and preserve rollback. Code returns the address and clears return data;
Memory returns child data and writes the requested slice. These boundaries
are deliberately about `handle_exception NONE`, not `handle_step NONE`:
Code deposit still precedes settlement in the latter. Checked build:
TO_seq58_prog_call_rules-20261030T133624Z_m0322_t001.

### Empty-output deposit and final tail coverage map

The independent probe checks `handle_create_empty_memory_exact` (identity
apart from reraising NONE) and `handle_create_empty_code_exact` (explicit
empty-code account update). It also checks `handle_step_empty_memory_exact`
and `handle_step_empty_code_exact`, factoring successful handling into these
deposit boundaries followed by the already checked success settlement
boundaries. Code's zero gas charge still requires `c.gasUsed <= gasLimit`.
These create equations are typed at unit execution_result to avoid an
unconstrained polymorphic reraise result when chaining them into handle_step.
Final checked probe build: TO_seq58_prog_call_rules-20261030T133624Z_m0350_t001.

Consumer mapping (no frozen proof edited at this checkpoint):
- Invalid outermost/inner: the exact Invalid settlement boundaries above;
  child meter bound comes from wf_context, with parent stack room for inner.
- SELFDESTRUCT outermost/inner: `step_self_destruct_def` explicitly clears
  returnData before consuming execution gas, then charges state gas. Frozen
  consumers assume `g + gasCost <= p.gasLimit` and `stateCost <= sg`, so this
  charge has no spill and leaves used gas `g + gasCost <= p.gasLimit`.
  Thus both empty-output deposit boundaries apply. Compose the corresponding
  handle_step bridge with singleton success or inner Memory/Code success.
  Inner unused-grant and stack-room guards are explicit frozen premises;
  arbitrary refunds/logs and both output destinations are covered.
  Code updates accounts even though its deposit costs are zero. The named
  frozen inner merge subtracts unused child gas after repayment, whereas the
  helper subtracts before repayment; natural truncated-subtraction
  commutation reconciles these presentations, without a new gas bound.
- CALL precompile entry: `proceed_call_precompile_success_meter` plus its
  zero-refund specialization independently validate drained parent reservoir,
  child baseline, zero spill and commitment, transfer logs and output grant.
  `handle_step_success_memory_exact` supplies its successful Memory tail.
  `restored_unused_gas`, `_bound`, `_sub` supply failed-child grant arithmetic.
  `step_precompile_success_exact` remains C2 composition, dependent on the
  frozen `step_call_prepared`; it was deliberately not used to certify the
  independent machinery. Its full composition is not claimed proved here.
