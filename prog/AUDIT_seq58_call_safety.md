# Scoped callee safety / finite-return audit (C1.3.3)

This is an interface audit, not a proof of opcode preservation or the exports.
Checked arithmetic/record probes live in vfmCallMeterProbeScript.sml.

## Existing consumer contracts (source locations at audit time)

- spec/prop/vfmDecreasesGasScript.sml:2524-2560:
  `run_call_tr n (r,s)` is total by the lexicographic contexts_weight measure
  and decreases_gas_cred_step. No wf_state, meter-backing or collection premise.
  `run_call_eq_tr: run_call es = SOME
  (run_call_tr (LENGTH es.contexts) (step es))` is unconditional. Thus
  termination is already solved, independently of exception safety.
- spec/prop/vfmAccountFrameScript.sml:151-166:
  `run_call_finite_trace: run_call es = SOME (r,t) ==> ?n.
  FUNPOW (step o SND) n (INL (),es) = (r,t) /\
  ~(ISL r /\ LENGTH es.contexts <= LENGTH t.contexts) /\
  !k. k<n ==> ISL (FST (FUNPOW (step o SND) k (INL (),es))) /\
  LENGTH es.contexts <= LENGTH (SND (FUNPOW (step o SND) k (INL (),es))).contexts`.
  No safety premise; an abort is a finite result too.
- Same file:74-86:
  `run_call_reaches_inv: Q es /\
  (!s u t. Q s /\ LENGTH es.contexts <= LENGTH s.contexts /\
    step s = (INL u,t) ==> Q t) /\ run_call_reaches es s ==> Q s`.
  This propagates an already proved invariant; it does not provide one.
- prog/vfmProgCallScript.sml:1293-1376:
  call_exn_safe_step_call claims safety from merely nonempty contexts.
  Historical E0011 refutes that claim. Its direct consumers are
  call_exn_safe_step_inst, call_exn_safe_step_inner and
  step_inner_not_impossible_unimplemented. Non-CALL primitive safety
  combinators need not be discarded, but this implication chain must change.
- Main file:1395-1443:
  `step_collect_ge2_inl: wf_state s /\ s.msdomain=Collect dd /\
  2<=LENGTH s.contexts /\ step s=(r,t) ==> ISL r`.
  Proof excludes OutsideDomain using collection mode, and excludes
  Impossible/Unimplemented via the false unrestricted inner safety chain.
  Handler side conditions are provided by step_inner_handler_state.
  `run_call_collect_inl` has the same entry premises and
  `run_call es=SOME(r,t) ==> ISL r`; OWHILE invariant currently contains
  only ISL, wf_state and collection mode. It needs the new scoped invariant.
- Main file:1445-1457:
  `run_call_collect_returns: wf_state es /\ es.msdomain=Collect dd /\
  2<=LENGTH es.contexts ==> ?t dd'. run_call es=SOME(INL(),t) /\
  LENGTH t.contexts+1=LENGTH es.contexts /\ t.msdomain=Collect dd'`.
  Existence uses unconditional total run_call_eq_tr; INL uses the broken
  collection lemma; exact length uses existing run_call_inl_length.
- Main file:1482-1518:
  `run_call_last_pop: wf_state es /\ run_call es=SOME(INL(),t) ==>`
  existence of n,before,err,mid with FUNPOW prefix, run_call_reaches,
  wf_state before, LENGTH before.contexts=LENGTH es.contexts,
  TL before.contexts=TL es.contexts, unchanged txParams, final step INL,
  step_inner before=(INR err,mid), handle_step err mid=(INL(),t).
  Its statement does not assert exception safety; conditional on INL it
  uses generic trace/length/outer-context invariants and should remain reusable.
- Main file:1559-1582:
  call_memory_final_pop additionally takes entry stack
  `(callee,saved)::(caller,cb)::rest`, Memory output, reached before at
  entry depth with unchanged tail, step_inner/handle_step final pop equations,
  and final length. It currently concludes the OLD gasUsed=caller.gasUsed-
  gasLeft formula with no state-gas fields. Must be restated using actual
  restore/absorb/credit/repay, not merely have its tactic repaired.
- Main file:2340-2373:
  call_returns_summary takes wf_state of pre-CALL state, parsed CALL opcode,
  prepared state/rollback/Collect equality, cg<=caller.gasUsed, stack room,
  non-precompile address and explicit step_call branch equation. It concludes
  finite successful trace, wf_state, collection, txParams, gasLeft<=cg,
  OLD returned caller record, rollback on failure and stipend observations.
  It must gain exact meter-transform outputs and guarded credited abort shape.
  Its entered branch obtains wf_state entry from step_preserves_wf_state,
  then invokes collection returns and final-pop machinery. The root callee
  is fresh, regardless of the suspended caller's meter.

## Existing invariants are insufficient

wf_context (ExecutionProp:118) bounds stack and gasUsed<=gasLimit and checks
parsed code only. wf_state (171) adds stack-room, accounts, depth, output and
gas_stack_ok. gas_stack_ok (164) bounds each parent's gasUsed by the sum of
`gasLimit-gasUsed+stateGasSpilled` in descendants. It neither includes the
parent's OWN refundable meter nor descendant stateGasCommitted. E0013 checks
why adding only per-frame backing fails across a returned grant.

handle_step_not_abort_returns_inl (ContextLength:113) requires handler equation,
depth>=2, EVERY wf_context, stack_room_ok, gas_stack_ok and non-abort error.
It is already checked; the missing piece is excluding abort errors of inner
execution on reachable callee-prefix states, not replacing total termination.

## Proposed scoped interface (NOT yet defined/proved in production)

Use checked probe `claim c = gasLimit-gasUsed+spill+committed`.
For entry depth n>=2, ceiling cg, and state s define conceptually:

```
prefix n s = TAKE (LENGTH s.contexts - n + 1) (MAP FST s.contexts)
budget n cg s <=>
  LENGTH s.contexts < n \/
  (SUM (MAP claim (prefix n s)) <= cg /\
   !i. i < LENGTH (prefix n s) ==>
     (EL i (prefix n s)).stateGasSpilled +
     (EL i (prefix n s)).stateGasCommitted +
     SUM (MAP claim (TAKE i (prefix n s))) <=
     (EL i (prefix n s)).gasUsed)
```

The external caller and all its ancestors are excluded. The ceiling is the
fresh root's grant, not an external backing constraint. The post-root-pop
case imposes no meter condition on that caller. wf_state is kept separately.

Exact proposed outputs for planning (names provisional, not new components):

1. `budget (LENGTH rest+2) tx.gasLimit
   (s with contexts := (initial_context a code static out charged sg tx,rb)::
      (external,externalSaved)::rest)`.
   Provider: fresh root backing and claim equality checked; list arithmetic
   remains. There is no premise on external.
2. `wf_state s /\ budget n cg s /\ 2<=n /\ n<=LENGTH s.contexts /\
   step s=(INL(),t) ==> budget n cg t`.
   Missing: opcode-wide and handler preservation including precompiles,
   CREATE deposit and failed charge/exception states. Do not claim checked.
3. `wf_state s /\ budget n cg s /\ 2<=n /\ n<=LENGTH s.contexts /\
   step_inner s=(INR e,t) ==> e<>SOME Impossible /\ e<>SOME Unimplemented`.
   Local CALL safety should require ONLY top-frame backing, obtained from
   budget at i=0; non-CALL safe primitives can be reused. This does not add
   a premise to an export: item 1 initializes budget in the entered child.
4. `wf_state es /\ budget (LENGTH es.contexts) cg es /\
   es.msdomain=Collect dd /\ 2<=LENGTH es.contexts ==>
   ?t dd'. run_call es=SOME(INL(),t) /\
   LENGTH t.contexts+1=LENGTH es.contexts /\ t.msdomain=Collect dd'`.
   Provider: existing totality/length/collection facts plus missing 2-3.
5. At reached states before final pop, combine budget root ceiling and top
   backing with step_inner/handle_create meter preservation to bound the
   ACTUAL refund after restoration by cg. Then use exact pop equation with
   cg<=caller.gasUsed and exact record output; no external caller backing.
   Main final-pop/summary statements need this interface and meter transforms.

## Checked implications and outstanding cases

- call_meter_initial_claim: fresh root claim is exactly tx.gasLimit.
- call_meter_stipend_push_budget: if sp+sc<=g, stipend<=cost and the newly
  charged usage g+cost+d+grant<=limit, then the suspended-parent margin covers
  fresh child grant+stipend, and parent+child total claim <= old parent claim.
  Thus the stipend is paid by the opcode cost, not by an external premise.
  Remaining semantic connection: consume/charge/grant equations, value-cost
  covering stipend, and all failed/intermediate branches.
- call_meter_restore_claim: ordinary handle_exception restoration subtracts
  ONLY spill from gasUsed and resets spill, retaining committed. Its claim is
  unchanged under backing and wf gas limit. Do NOT conflate this with full
  restore_state_gas_to_entry, which subtracts BOTH spill and committed.
  Existing call_meter_restore_grant arithmetic refers to full entry restoration;
  its comment has been corrected to make this distinction explicit.
- call_meter_forfeit_claim: actual forfeit succeeds on a backed wf meter,
  yields gasUsed=gasLimit, preserves backing and decreases claim. This covers
  exceptional rather than REVERT refund arithmetic, but not handler composition.
- call_meter_success_pop_claim: adjacent backed margin makes successful
  absorb/repay conserve parent+child total claim. This is the missing currency
  for higher ancestors, not only the immediate parent's own backing.
- call_meter_credit_claim: credit cancels the same MIN from usage and spill,
  preserving claim for a backed wf frame. Together with E0013 failure backing
  it explains creation-charge cancellation after a failed child; semantic
  restore/forfeit/pop sequencing still needs integration.

Mandatory next strategy checkpoint must add real executable leaves for list
budget interfaces/initialization, primitive meter and grant preservation,
scoped inner CALL safety, all-opcode/handler preservation, reachable collection
return, final-pop meter summary and stipend observations. These are proposals
for strategist evaluation, not an executor-created proof queue. C1.4 must not
start merely because the probes build.

## Final port validation (C1.7)

Both public CALL rules and all three shared specification tactics now build.
Compared with the original exports at `5f53d9b6`:

- `IMP_EVM_SPEC_FINITE` and `IMP_EVM_SPEC_FINITE_CODE` retain their statements.
- `caller_observation_frame` adds only the four state-gas projection guards.
- Both CALL preconditions retain all original stack, memory, delegation,
  static-mode, non-precompile and Collect-domain conditions. Creation is charged
  by the state-gas triplet; execution cost is written literally and has no
  `new_account_cost`. The only additional admissibility condition beyond reservoir
  coverage is the explicitly authorized `creditBack = MIN stateCost sp` and
  `calleeGas <= g + gasCost - creditBack` amendment (E0009 remains historical
  evidence against the original unamended contract).
- Existing rollback, return-data, unused-child-gas, logs and refund observations
  are retained. The stipend rule retains its successful account/toDelete
  footprint and frames originalAccounts. The general rule still owns
  originalAccounts. The new merged carrier specifies exact semantic settlement,
  independently of the child unused execution-gas witness.
- No external-caller backing assumption, zero-spill restriction, balance/depth
  check, or callee-code hypothesis was added.

The complete target rebuilt from dependencies in the final proof checkpoint.
A subsequent successful build checks an explicit kernel-tag assertion for all
five required exports: only empty tags or DISK_THM are accepted, including
transitive dependencies. This installation emits Theory.dat rather than
Theory.txt; the assertion checks the actual theorem tags directly. No parser or
cheat warning was emitted. The main script contains no cheat, axiom, mk_thm,
TRY/ORELSE search, or raw automation probe. All task changes are under prog/;
no tactic-timeout setting or semantics source was modified.

The old STATE cursor describes the pre-completion resume location; it is
superseded by reviewed component evidence E0062 and this final audit, not a
remaining proof obligation.
