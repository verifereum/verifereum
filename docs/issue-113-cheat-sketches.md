# Issue #113 — Concrete sketches for the 6 remaining cheats

This document gives a concrete, tactic-level sketch for each of the
remaining cheats. Sketches are in draft-style HOL4 tactic script.

---

## 1. `step_create_inr_no_grow` (`vfmCallFrameScript.sml` line 3011)

**Statement:**

```hol
s.contexts ≠ [] ∧ step_create two s = (INR e, s') ⇒
LENGTH s'.contexts = LENGTH s.contexts
```

**Why true:** `step_create` has shape `prefix >>= (λ_. if c1 then abort_unuse
else if c2 then abort_create_exists else proceed_create)`. Only
`proceed_create` pushes a context, and `proceed_create_returns_inl`
guarantees it never returns INR. So any INR result came from the prefix
or the abort branches, neither of which push.

**Sketch:**

```hol
Proof
  strip_tac
  >> mp_tac same_frame_or_grow_step_create
  >> rewrite_tac[same_frame_or_grow_def]
  >> disch_then drule >> simp[]
  >> strip_tac
  >- gvs[same_frame_rel_def]  (* same-frame case: length preserved *)
  (* Grow case: LENGTH s'.contexts ≥ LENGTH s.contexts + 1. Derive F. *)
  >> qpat_x_assum `step_create _ _ = _` mp_tac
  >> simp[step_create_def]
  (* Peel off the prefix. Each primitive is preserves_same_frame, so
     its INR result (if any) doesn't grow. Use pairarg_tac after each
     to introduce the intermediate state. *)
  >> simp[bind_def, ignore_bind_def]
  (* pop_stack *)
  >> Cases_on `pop_stack (if two then 4 else 3) s` >> simp[]
  >> Cases_on `q` >> simp[]
  >- (
    (* INR case: pop_stack failed. No grow. *)
    strip_tac >> gvs[]
    >> `preserves_same_frame (pop_stack (if two then 4 else 3))` by simp[]
    >> drule_then drule psf_imp_length_contexts_preserved >> simp[])
  (* INL case: continue through memory_expansion_info, consume_gas, ... *)
  (* For each intermediate primitive, case on INL/INR and show INR
     doesn't grow via preserves_same_frame. For the final 3-way if,
     abort_unuse / abort_create_exists have preserves_same_frame,
     and proceed_create returns INL (by proceed_create_returns_inl),
     contradicting our INR hypothesis. *)
  >> ...  (* 15+ more primitives in step_create's prefix *)
QED
```

**Tedium:** High. ~15 primitives in the prefix; each needs the same
case-INL-INR pattern. Maybe 100+ lines. Could be automated with a
bespoke tactic that repeats the pattern.

**Alternative:** Define a stronger `same_frame_or_grow_strict m` that
additionally tracks the result: `m s = (INR _, _) ⇒ same_frame_rel s s'`.
Prove composition lemmas for it, then show `step_create two` satisfies
it. This requires duplicating the `same_frame_or_grow` framework but
makes the final step a single `>> simp[same_frame_or_grow_strict_def]`.

---

## 2. `handle_exception_pop_failure_memory_effect` (line 3151)

**Statement:**

```hol
s.contexts = (callee, callee_rb) :: parent :: rest ∧
callee.msgParams.outputTo = Memory mr ∧
handle_exception e s = (q, s') ⇒
  s'.rollback = callee_rb ∧
  (∃new_parent_ctx.
     s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
     new_parent_ctx.msgParams = (FST parent).msgParams ∧
     new_parent_ctx.logs = (FST parent).logs ∧
     new_parent_ctx.addRefund = (FST parent).addRefund ∧
     new_parent_ctx.subRefund = (FST parent).subRefund)
```

**Issue with current statement:** As written, the theorem is too strong
for ALL `e`. For `e = NONE`, handle_exception takes the success path with
possible finalisation on Memory. For `e = SOME Reverted`, it takes the
`else` branch skipping `consume_gas`, then still pops. For other `e ≠
NONE`, it consumes gas first. All paths with `n > 1` end with
`pop_and_incorporate_context success; inc_pc; <Memory finalisation>`.

**Sketch:**

```hol
Proof
  strip_tac
  >> simp[handle_exception_def, bind_def, ignore_bind_def]
  (* Case on e = NONE / e = SOME Reverted / other *)
  >> gvs[get_num_contexts_def, return_def,
         get_return_data_def, get_output_to_def,
         inc_pc_def, get_current_context_def,
         set_current_context_def,
         set_return_data_def, push_stack_def,
         write_memory_def, reraise_def,
         get_gas_left_def, consume_gas_def, assert_def, fail_def]
  (* After unfold, the state has:
       - pop_and_incorporate_context success applied (use pop lemma #6)
       - inc_pc, set_return_data, push_stack on the new head
       - write_memory for the Memory output case *)
  (* Need n = LENGTH s.contexts = SUC (SUC (LENGTH rest)) > 1.
     The `n ≤ 1` branch is false, so we go into the pop branch. *)
  >> Cases_on `e`
  >- (  (* e = NONE: success path *)
    (* handle_exception with e = NONE: success = T, skip consume_gas/
       set_return_data, go to n > 1 branch.
       pop_and_incorporate_context T uses the success branch of
       pop_and_incorporate which we haven't proved a lemma for yet —
       BUT we need the FAILURE effect (s'.rollback = callee_rb).
       On SUCCESS pop, rollback is KEPT, not set to callee_rb!
       So for e = NONE, s'.rollback = s.rollback ≠ callee_rb in general.
       HYPOTHESIS CHANGE NEEDED: require e ≠ NONE. *)
    ...)
  ...
QED
```

**Plan flaw detected:** The theorem as stated is FALSE for `e = NONE`.
When `e = NONE`, handle_exception takes the success pop path, and
`set_rollback` is NOT called — so `s'.rollback = s.rollback`, which is
NOT `callee_rb` in general (it's whatever the child accumulated).

**Fix:** Add `e ≠ NONE` hypothesis. Then:

```hol
Proof
  strip_tac
  >> `¬(e = NONE)` by gvs[]  (* from the added hyp *)
  >> `LENGTH s.contexts > 1` by (Cases_on `rest` >> simp[])
  >> simp[handle_exception_def, bind_def, ignore_bind_def]
  >> simp[get_num_contexts_def, return_def, get_return_data_def,
          get_output_to_def, get_current_context_def]
  >> `(FST (HD s.contexts)).msgParams.outputTo = Memory mr` by simp[]
  >> (* Unfold the e = SOME _ branch: e ≠ NONE. Also consider
        e = SOME Reverted separately (skips consume_gas). *)
  >> Cases_on `e` >> gvs[]
  (* Thread through pop_and_incorporate_context_failure_effect, then
     inc_pc, set_return_data, push_stack, write_memory. *)
  >> imp_res_tac pop_and_incorporate_context_failure_effect
  >> ...
QED
```

**Tedium:** Medium. Mostly unfolding + using the pop lemma.
~50 lines.

---

## 3. `handle_step_pop_memory_effect` (line 3175)

**Statement:**

```hol
s.contexts = (callee, callee_rb) :: parent :: rest ∧
(∃mr. callee.msgParams.outputTo = Memory mr) ∧
¬ vfm_abort e ∧
handle_step e s = (q, s') ⇒
  s'.rollback = callee_rb ∧
  (∃new_parent_ctx.
     s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
     new_parent_ctx.msgParams = (FST parent).msgParams ∧
     new_parent_ctx.logs = (FST parent).logs ∧
     new_parent_ctx.addRefund = (FST parent).addRefund ∧
     new_parent_ctx.subRefund = (FST parent).subRefund)
```

**Same plan flaw:** fails for `e = NONE`.

**Fix + sketch:**

```hol
Proof
  strip_tac
  >> `e ≠ NONE` by cheat  (* TODO: add as hypothesis, same as above *)
  >> simp[handle_step_def]
  >> `¬vfm_abort e` by simp[]
  (* handle_step calls handle (handle_create e) handle_exception.
     With outputTo = Memory mr, handle_create_reraises applies:
     handle_create e s = reraise e s = (INR e, s). *)
  >> `handle_create e s = (INR e, s)` by (
       drule handle_create_reraises
       >> simp[])  (* needs lookup for handle_create_reraises *)
  >> simp[handle_def]
  >> (* now goal: handle_exception e s = (q, s') ⇒ ... *)
  >> drule_all handle_exception_pop_failure_memory_effect
  >> simp[]
QED
```

**Prerequisite:** `handle_create_reraises` from `vfmStaticCallsScript`.
Need to check exact name and signature.

**Tedium:** Low (given cheat #2 is proven). ~15 lines.

---

## 4. `step_call_inr_grow_structure` (line 3214)

**Statement:**

```hol
s.contexts ≠ [] ∧ outputTo_consistent s ∧
step_call op s = (INR e, s1) ∧
LENGTH s1.contexts > LENGTH s.contexts ⇒
  ¬ vfm_abort e ∧
  (∃sp callee_ctx callee_rb mr.
     same_frame_rel s sp ∧
     callee_rb = sp.rollback ∧
     (∃parent_ctx.
        s1.contexts = (callee_ctx, callee_rb) ::
                      (parent_ctx, SND (HD sp.contexts)) ::
                      TL sp.contexts ∧
        parent_ctx.msgParams = (FST (HD sp.contexts)).msgParams ∧
        parent_ctx.logs = (FST (HD sp.contexts)).logs ∧
        parent_ctx.addRefund = (FST (HD sp.contexts)).addRefund ∧
        parent_ctx.subRefund = (FST (HD sp.contexts)).subRefund) ∧
     callee_ctx.msgParams.outputTo = Memory mr)
```

**Structure of `step_call`:** approx.

```
pop_stack(6+valueOffset);  -- INR: no grow
let gas, address, ...;
memory_expansion_info;      -- INR: no grow
access_address address;     -- INR: no grow
<compute delegate code>;    -- INR: no grow (possibly further access_address)
let dynamicGas, stipend;
consume_gas ...;            -- INR: no grow
if Call ∧ value>0 then assert_not_static else return ();  -- INR: no grow
expand_memory;              -- INR: no grow
sender <- get_callee;       -- INR: no grow
if balance<value then abort_call_value else
  set_return_data [];
  sucDepth <- get_num_contexts;
  if sucDepth > 1024 then abort_unuse else
    proceed_call ...        -- can grow
```

Inside `proceed_call`:

```
rollback <- get_rollback;   -- captures sp.rollback
read_memory;
transfer_value(if valued);
get_caller; get_value; get_static;
push_context(ctx, rollback);  -- GROWS here
if address ∈ precompile_addresses then dispatch_precompiles address
else return ();              -- dispatch_precompiles can INR
```

**Key observations:**
- `sp` = state just before `push_context`. Since all primitives from
  `s` to `sp` are `preserves_same_frame`, `same_frame_rel s sp`.
- After `push_context(ctx, rollback)`, state has
  `contexts = (ctx, sp.rollback) :: sp.contexts`.
- `dispatch_precompiles address` is called with head = the new callee.
  If it fails with INR, state unchanged except callee's head (via
  consume_gas etc.). Crucially, it operates ON the callee context,
  leaving parent unchanged (parent is tail[0]).
- So `s1.contexts = (callee_modified, sp.rollback) :: sp.contexts`
  = `(callee_modified, sp.rollback) :: (FST (HD sp.contexts), SND (HD sp.contexts)) :: TL sp.contexts`.
- Here `parent_ctx = FST (HD sp.contexts)` — the parent's head after
  the prefix.
- `outputTo = Memory {offset:=retOffset; size:=retSize}` per
  `proceed_call`.
- Precompile failures: `fail OutOfGas`, `fail InvalidParameter`,
  `fail KZGProofError`. None are `vfm_abort`.

**Sketch (high-level):**

```hol
Proof
  strip_tac
  (* First: derive op is Call/CallCode/DelegateCall/StaticCall.
     This follows from same_frame_or_grow_step_call + the grow
     hypothesis: step_call for non-Call ops doesn't exist at this
     point (step_call IS for Call family). Trivially true. *)
  >> simp[step_call_def, bind_def, ignore_bind_def]
  >> qpat_x_assum `step_call _ _ = _` mp_tac
  (* Peel each primitive of the prefix, tracking the intermediate
     state and preserving same_frame_rel. Use preserves_same_frame
     composition + same_frame_rel_refl as initial. *)
  (* Let sp0, sp1, ..., spk be the intermediates. Each transition
     is preserves_same_frame, so same_frame_rel s sp_i by
     transitivity. *)
  >> simp[pop_stack_def, memory_expansion_info_def, access_address_def,
          get_accounts_def, get_delegate_def,
          get_gas_left_def, consume_gas_def, assert_def, assert_not_static_def,
          expand_memory_def, get_callee_def, set_return_data_def,
          get_num_contexts_def, abort_call_value_def, abort_unuse_def,
          domain_check_def, fail_def, return_def,
          get_current_context_def, set_current_context_def,
          bind_def, ignore_bind_def, AllCaseEqs()]
  >> rpt strip_tac >> gvs[]
  (* After many case splits, we reach the proceed_call path.
     The INR with grow must come from dispatch_precompiles. *)
  >> simp[proceed_call_def, bind_def, ignore_bind_def,
          get_rollback_def, read_memory_def, update_accounts_def,
          push_context_def, get_caller_def, get_value_def, get_static_def,
          return_def, AllCaseEqs()]
  >> ...
  (* At this point sp = state just before push_context = s after prefix.
     qexists_tac sp. *)
  >> qexists_tac `sp`  (* explicit state *)
  (* Show same_frame_rel s sp by composing preserves_same_frame lemmas
     for every primitive in the prefix. Use the existing [simp] lemmas
     for each (e.g. preserves_same_frame_pop_stack etc.). *)
  >> simp[]
  (* Verify the rest of the structure: callee_ctx, parent_ctx, etc. *)
  >> ...
  (* Finally: the exception is not vfm_abort. Case on precompile
     address: dispatch_precompiles routes to specific precompile, all
     of which only fail with OOG / InvalidParameter / KZGProofError. *)
QED
```

**Tedium:** Very high. This is the single largest state-level lemma.
Probably 300+ lines. Much of it can be abstracted via a "prefix
preserves same_frame" meta-theorem stated at the function level: i.e.,
define the prefix as a specific monad, prove it `preserves_same_frame`,
then argue from there.

**Recommended decomposition:** Define helper

```hol
Definition step_call_prefix_def:
  step_call_prefix op = do
    valueOffset <<- if call_has_value op then 1 else 0;
    args <- pop_stack (6 + valueOffset);
    (* ... up to but not including proceed_call ... *)
    gasLeft <- get_gas_left;
    (dynamicGas, stipend) <<- call_gas ...;
    consume_gas $ static_gas op + dynamicGas + mx.cost;
    if op = Call ∧ 0 < value then assert_not_static else return ();
    expand_memory mx.expand_by;
    sender <- get_callee;
    ...
  od
End
```

Prove `preserves_same_frame (step_call_prefix op)` using composition
(~10 lines). Then `step_call op = step_call_prefix op >> ...`.

Also define:

```hol
Definition proceed_call_pre_push_def:
  proceed_call_pre_push op sender address value argsOffset argsSize = do
    rollback <- get_rollback;
    data <- read_memory argsOffset argsSize;
    if op ≠ CallCode ∧ 0 < value then
      update_accounts $ transfer_value sender address value
    else return ();
    caller <- get_caller;
    ...
    (* everything up to push_context *)
  od
End
```

Prove this is `preserves_same_frame`. Then the big lemma reduces to:
"after the prefix + push_context + dispatch_precompiles, the structure
is as claimed".

---

## 5. `step_call_handle_step_inr_grow_same_frame` (line 3271)

**Statement:**

```hol
s.contexts ≠ [] ∧ outputTo_consistent s ∧
step_call op s = (INR e, s1) ∧
LENGTH s1.contexts > LENGTH s.contexts ∧
handle_step e s1 = (q, s') ∧
LENGTH s'.contexts = LENGTH s.contexts ⇒
same_frame_rel s s'
```

**Sketch:** (already written in the comments of the file; just needs
to be mechanised)

```hol
Proof
  strip_tac
  (* Step 1: Extract structure from step_call_inr_grow_structure. *)
  >> drule_all step_call_inr_grow_structure
  >> strip_tac
  (* Now we have: ¬vfm_abort e, same_frame_rel s sp, callee_rb = sp.rollback,
     s1.contexts = (callee_ctx, callee_rb) ::
                   (parent_ctx, SND (HD sp.contexts)) :: TL sp.contexts,
     parent_ctx.msgParams = (FST (HD sp.contexts)).msgParams,
     ... parent_ctx.addRefund/subRefund = ...,
     callee_ctx.msgParams.outputTo = Memory mr. *)
  (* Step 2: Apply handle_step_pop_memory_effect. *)
  >> qpat_x_assum `handle_step e s1 = _` mp_tac
  >> `s1.contexts = (callee_ctx, callee_rb) :: (parent_ctx, SND (HD sp.contexts)) :: TL sp.contexts`
     by simp[]
  >> disch_then (fn th => drule handle_step_pop_memory_effect
                          >> disch_then (qspecl_then [...] mp_tac)
                          >> impl_tac)
  (* ... *)
  >> strip_tac
  (* Now we have s'.rollback = callee_rb = sp.rollback,
     s'.contexts = (new_parent_ctx, SND (HD sp.contexts)) :: TL sp.contexts,
     new_parent_ctx.msgParams = parent_ctx.msgParams = (FST (HD sp.contexts)).msgParams,
     etc. *)
  (* Step 3: Verify each same_frame_rel conjunct. *)
  >> simp[same_frame_rel_def]
  >> rpt conj_tac
  >- (gvs[])  (* s.contexts ≠ [] *)
  >- (gvs[])  (* LENGTH s'.contexts = LENGTH s.contexts *)
  >- (  (* TL s'.contexts = TL s.contexts *)
    `TL s'.contexts = TL sp.contexts` by simp[]
    >> `TL sp.contexts = TL s.contexts` by metis_tac[same_frame_rel_def]
    >> simp[])
  >- (  (* SND (HD s'.contexts) = SND (HD s.contexts) *)
    `SND (HD s'.contexts) = SND (HD sp.contexts)` by simp[]
    >> `SND (HD sp.contexts) = SND (HD s.contexts)` by metis_tac[same_frame_rel_def]
    >> simp[])
  >- (  (* head msgParams equal *)
    `(FST (HD s'.contexts)).msgParams = (FST (HD sp.contexts)).msgParams` by simp[]
    >> metis_tac[same_frame_rel_msgParams])
  >- (  (* s'.txParams = s.txParams *)
    (* handle_step doesn't touch txParams; trace through handle_step_def
       for this. *)
    cheat)  (* Could be an auxiliary lemma. *)
  >- (  (* callee_local_changes callee s.rollback s'.rollback *)
    `s'.rollback = sp.rollback` by simp[]
    >> metis_tac[same_frame_rel_def])
  >- (  (* accesses_grow *)
    `s'.rollback.accesses = sp.rollback.accesses` by simp[]
    >> metis_tac[same_frame_rel_def])
  >- (  (* msdomain_compatible *)
    (* This is the trickiest: sp -> s1 may grow msdomain (precompile
       in Collect mode). s1 -> s' is a pop (no msdomain change).
       So s'.msdomain = s1.msdomain ⊇ sp.msdomain ⊇ s.msdomain. *)
    cheat)  (* Needs handle_step_preserves_msdomain (not yet stated). *)
  >- (  (* IS_PREFIX logs *)
    `(FST (HD s'.contexts)).logs = (FST (HD sp.contexts)).logs` by simp[]
    >> metis_tac[same_frame_rel_def])
  >- (  (* addRefund monotone *)
    `(FST (HD s'.contexts)).addRefund = (FST (HD sp.contexts)).addRefund` by simp[]
    >> metis_tac[same_frame_rel_def])
  >- (  (* subRefund monotone *)
    `(FST (HD s'.contexts)).subRefund = (FST (HD sp.contexts)).subRefund` by simp[]
    >> metis_tac[same_frame_rel_def])
QED
```

**Tedium:** Medium. Mostly mechanical once #4 is in place. ~80 lines.

**Remaining cheats in sketch:** `txParams` preservation through
handle_step (easy, just unfold), and `msdomain_compatible` through
handle_step (requires showing handle_step only modifies msdomain by
adding to Collect sets).

---

## 6. `run_call_inv_step` (`vfmRunCallScript.sml` line 169)

**Statement:**

```hol
∀es s s' r.
  es.contexts ≠ [] ∧
  run_call_inv es s ∧
  LENGTH s.contexts ≥ LENGTH es.contexts ∧
  step s = (r, s') ⇒
  run_call_inv es s'
```

**Sketch:**

```hol
Proof
  rpt strip_tac
  (* Unfold run_call_inv *)
  >> gvs[run_call_inv_def]
  >> conj_asm1_tac
  >- (  (* s'.txParams = es.txParams *)
    (* Requires `step_preserves_txParams` from vfmTxParamsScript. *)
    metis_tac[step_preserves_txParams])
  (* Now: EVERY (...) (active_rollbacks ... s') *)
  (* Case analysis on length change: *)
  >> `s.contexts ≠ []` by (Cases_on `s.contexts` >> gvs[]
                           >> Cases_on `es.contexts` >> gvs[])
  >> Cases_on `LENGTH s'.contexts = LENGTH s.contexts`
  >- (  (* Same-frame case *)
    (* Use step_same_frame. Needs outputTo_consistent s, which
       requires threading that through run_call_inv too, OR
       establishing via an auxiliary invariant. *)
    cheat)
  >> Cases_on `LENGTH s'.contexts > LENGTH s.contexts`
  >- (  (* Grow case: push happened *)
    (* New active_rollbacks has an extra entry at position 1:
       the saved rb of the freshly pushed context. That saved rb
       was s.rollback at the push point (post-prefix), which has
       storage_slot_preserved against es.rollback because the prefix
       is preserves_same_frame and accesses are monotone. *)
    cheat)
  (* Shrink case *)
  >> `LENGTH s'.contexts < LENGTH s.contexts` by decide_tac
  >> (* Pop happened. s'.rollback = s.rollback (success) or
        = SND (HD s.contexts) (revert, from pop_and_incorporate). 
        In either case, it's an entry in the old active_rollbacks,
        so the invariant for that entry carries over. *)
  cheat
QED
```

**Dependencies (not yet available):**

- `step_preserves_txParams`: probably exists in `vfmTxParamsScript`.
  Need to check.
- `outputTo_consistent` threading: `step_same_frame` requires
  `outputTo_consistent s`. Either add that to `run_call_inv` or
  establish it separately via initial-state assumption + preservation
  under step. Similar to the within-frame case.
- Characterisation of step's push and pop effects on `rollback`:
  - Push: `s'.rollback.accounts = s.rollback.accounts` modulo
    `transfer_value` and `increment_nonce(senderAddress)` for CREATE.
    Both of these only change BALANCES and NONCES, not storage slots.
    So `storage_slot_preserved s'.rollback s.rollback` at the slot level.
    New saved rb in s'.contexts is `s.rollback` at mid-step, which by
    the same reasoning has `storage_slot_preserved mid_rb s.rollback`.
  - Pop success: `s'.rollback = s.rollback` (pop doesn't change it),
    `s'.contexts = TL s.contexts` plus some head modifications (pc,
    stack). Active_rollbacks for `s'` is a sub-prefix of active_rollbacks
    for `s`.
  - Pop revert: `s'.rollback = SND (HD s.contexts)` (the popped head's
    saved rb). This was already entry 1 of the old `active_rollbacks`,
    so it satisfies the invariant.

**Helper lemmas needed:**

```hol
Theorem step_push_active_rollbacks:
  step s = (r, s') ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
  ∃mid_rb.
    MAP SND s'.contexts = mid_rb :: MAP SND s.contexts ∧
    storage_slot_preserved mid_rb s.rollback ∧
    s'.rollback = s.rollback  (* modulo transfer_value/increment_nonce
                                  which don't affect storage *)

Theorem step_pop_success_active_rollbacks:
  step s = (r, s') ∧ LENGTH s'.contexts < LENGTH s.contexts ⇒
  (s'.rollback = s.rollback ∨
   s'.rollback = SND (HD s.contexts))

Theorem step_same_frame_slot_preserved:
  same_frame_rel s s' ⇒
  storage_slot_preserved s'.rollback s.rollback
```

The last one is the crucial conversion. Proof: if `a ∉ s'.storageKeys`,
then (monotone) `a ∉ s.storageKeys`. By same_frame_rel's callee-local
conjunct: at non-callee accounts, storage is equal (so storage slot
equal). At callee: storage differs only via SSTORE which access-lists
the slot, putting it in s'.storageKeys, contradicting our hypothesis.

**Tedium:** Medium-high. The case analysis is clean but each case
requires characterising step's effect on `rollback` (which is a
separate proof). Probably 200+ lines total.

---

## Summary of tedium / risk

| # | Cheat | Lines | Risk |
|---|-------|-------|------|
| 1 | step_create_inr_no_grow | ~100 | Low (pure unfolding) — now reduced to `step_create_grown_returns_inl` |
| 2 | handle_exception_pop_failure_memory_effect | ~50 | Medium (flaw in current statement) |
| 3 | handle_step_pop_memory_effect | ~15 | **Actually surprisingly tricky** (see below) |
| 4 | step_call_inr_grow_structure | ~300 | High (largest) |
| 5 | step_call_handle_step_inr_grow_same_frame | ~80 | Medium (needs aux lemmas) |
| 6 | run_call_inv_step | ~200 | Medium-high (needs step-effect lemmas) |

**Total: ~750 lines of tactic code** for the 6 remaining cheats.

## Notes from attempted proof of cheat #3

Multiple attempts at `handle_step_pop_memory_effect` failed despite a
clear informal proof. The pattern is:

1. We establish `handle_create e s = reraise e s` via
   `handle_create_reraises` (requires outputTo ≠ Code _).
2. We establish `reraise e s = (INR e, s)` via `reraise_def`.
3. The goal (after unfolding `handle_step` and `handle`) becomes:
   `(case handle_create e s of (INL v, s'') ⇒ (INL v, s'') | (INR e, s'') ⇒ handle_exception e s'') = (q, s')`.
4. Substituting `handle_create e s` with `(INR e, s)` should reduce
   this to `handle_exception e s = (q, s')`.

But `simp`, `SUBST1_TAC`, `once_rewrite_tac`, `asm_simp_tac bool_ss/std_ss`
all failed to perform the substitution in step 4, for reasons unclear.
The assumption `handle_create e s = (INR e, s)` was present in
assumptions but did not fire.

Hypotheses (untested):
- Possibly the `e` in the case pattern `| (INR e, s'') ⇒` shadows the
  outer `e`, confusing simp's binding analysis.
- Possibly simp's rewrite orientation heuristic decided the LHS is
  "bigger" than the RHS, so it orients the equation as
  `(INR e, s) → handle_create e s`, which doesn't fire on occurrences
  of `handle_create e s` because the pattern doesn't match.

**Suggested workarounds for a future attempt:**
- Prove a local lemma `⊢ (case (INR e, s) of (INL v, t) ⇒ _ | (INR e', t) ⇒ h e' t) = h e s` and use that directly.
- Alpha-rename the bound `e` in the case pattern first using
  `CONV_TAC (RENAME_VARS_CONV ["e1"])` or similar.
- Use `CHANGED_TAC (RW.ONCE_RW_TAC [th])` or HOL's term rewriter
  (`termRewrite` or similar) with explicit substitution.
- Manually construct the goal using `conj_tac` / `exists_tac` /
  `qsuff_tac` rather than rewriting.

## Progress this session (4)

- **New helper lemmas** added:
  - `handle_step_pop_success_memory_effect` and
    `handle_exception_pop_success_memory_effect` (for e = NONE
    success pop path).
  - 15 `SND_*_msdomain` lemmas and `SND_handle_step_msdomain`
    chain, proving handle_step preserves msdomain exactly.
  - `abort_unuse_length` and `abort_create_exists_length`
    (preserve contexts length).
- **`step_call_inr_grow_structure` cheat conclusion strengthened**
  with `s1.rollback = sp.rollback` and `s1.msdomain = sp.msdomain`.
- **Cheat #5 `step_call_handle_step_inr_grow_same_frame`** — now
  discharged modulo 2 inner `q = INL ()` cheats plus the
  `step_call_inr_grow_structure` cheat. Factored into success
  (e = NONE) and failure (e ≠ NONE) branches. Non-trivial fact:
  same tactic works for both cases at the outer level because
  transitivity through `sp` + same_frame_rel handles it.
- Attempted `psf_or_inl_grow` predicate framework for cheat #1
  (`step_create_grown_returns_inl`). Discovered the predicate
  doesn't compose cleanly through bind when g can both grow AND
  have an INL result threaded into f which may fail (INR).
  Reverted the draft; cheat remains with detailed sketch in proof
  comment.
- Drafted structural outline for `run_call_inv_step` cheat in
  vfmRunCallScript with 3-way case analysis. Not yet proven.

Remaining cheats: 5 (down from 7 two sessions ago, 6 at start of
this session).

## Progress this session (3)

- Added `handle_step_pop_success_memory_effect` and
  `handle_exception_pop_success_memory_effect`: variants for the
  `e = NONE` case, where the pop is a success pop (rollback kept,
  logs/refunds grow).
- Added 15 new `SND_*_msdomain` simp lemmas and two top-level
  `SND_handle_exception_msdomain`, `SND_handle_create_msdomain`,
  `SND_handle_step_msdomain` showing handle_step preserves msdomain
  exactly.
- Strengthened `step_call_inr_grow_structure` cheat conclusion with
  `s1.rollback = sp.rollback` and `s1.msdomain = sp.msdomain`.
- **Cheat #5 `step_call_handle_step_inr_grow_same_frame`** — now
  discharged modulo 2 `q = INL ()` subcheats + the existing
  `step_call_inr_grow_structure` cheat. Factored into success
  (e = NONE) and failure (e ≠ NONE) branches with clean closure of
  each arm.
- Eliminated `e ≠ NONE` cheat (handled via case split on e = NONE).
- Eliminated `msdomain_compatible sp.msdomain s'.msdomain` cheat
  (followed from SND_handle_step_msdomain).
- Eliminated `s'.txParams = sp.txParams` cheat (followed from
  existing handle_step_preserves_txParams + step_call_preserves_txParams).

Remaining cheats: 5
- `step_create_grown_returns_inl` (helper for #1)
- `step_create_inr_no_grow`
- `step_inst_inr_grew_is_call_family` (depends on #1)
- `step_call_inr_grow_structure` (the big ~300-line one)
- two `q = INL ()` subgoals in `step_call_handle_step_inr_grow_same_frame`
- `run_call_inv_step` in vfmRunCallScript

(So 5 `cheat` occurrences in vfmCallFrameScript + 1 in
vfmRunCallScript = 6 literal cheats; but some are duplicates and
`q = INL ()` cheats are small.)

## Progress this session (2)

- **Cheat #2 `handle_exception_pop_failure_memory_effect`** — PROVEN.
  Weakened signature to require `handle_exception e s = (INL (), s')`
  (the failure case when consume_gas/unuse_gas fails would give INR
  with s' = s, which can't establish s'.rollback = callee_rb).
- **Cheat #3 `handle_step_pop_memory_effect`** — PROVEN by user,
  cleaned up. Correspondingly strengthened signature to require
  `handle_step e s = (INL (), s')`.
- **Cheat #1 `step_create_inr_no_grow`** — still cheated (reduced
  to `step_create_grown_returns_inl` which is also cheated).
- **Cheat #4 `step_call_inr_grow_structure`** — still cheated.
- **Cheat #5 `step_call_handle_step_inr_grow_same_frame`** — partial
  progress: the outer proof shape is in place using #4 and #3, but 4
  inner subcheats remain: `q = INL ()`, `e ≠ NONE`,
  `s'.txParams = sp.txParams`, `msdomain_compatible sp.msdomain
  s'.msdomain`.
- **Cheat #6 `run_call_inv_step`** — unchanged, still cheated.

Current cheat count: 8 total (7 in vfmCallFrameScript + 1 in
vfmRunCallScript). This is more than the 6 originally listed because
#5 was factored into subgoals with 4 residual cheats rather than one
large cheat.

## Key flaws identified during sketching

- **Cheats #2 and #3 (`handle_exception_pop_failure_memory_effect` and
  `handle_step_pop_memory_effect`) are FALSE as stated** for `e = NONE`
  (success case). Must add `e ≠ NONE` hypothesis. The users of these
  lemmas always have `e ≠ NONE` (precompile failures, etc.), so this
  is a safe restriction.

- Cheat #5 needs small auxiliary lemmas `handle_step_preserves_txParams`
  and `handle_step_msdomain_compatible` that aren't currently in the
  file.

- Cheat #6 needs new step-effect-on-rollback lemmas, which are separate
  proofs of moderate size.
