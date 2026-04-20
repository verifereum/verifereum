Issue #113 — remaining cheat: `run_call_inv_step`
=================================================

**Tracking:** <https://github.com/verifereum/verifereum/issues/113>

## Current status

The headline theorem `run_call_preserves_storage_outside_accessed_slots`
is proven modulo a single cheat: `run_call_inv_step` in
`spec/prop/vfmRunCallScript.sml` (line 208).

## Derisking summary (all checks passed)

- `cp_step_inst_non_call[simp]` covers ALL opcodes except the ten
  that genuinely modify storage or push: `SStore`, `TStore`, `Log n`
  (any n), `SelfDestruct`, `Create`, `Create2`, `Call`, `CallCode`,
  `DelegateCall`, `StaticCall`. These are the only cases that need
  direct argument.
- `msgParams` of each context is **immutable** once pushed: no
  step-level primitive modifies it. So `outputTo_consistent_stack`
  reduces to "every push introduces an outputTo-consistent child",
  which holds by construction (`initial_context callee _ _ outputTo _`
  gives `Memory mr` for step_call and `Code callee` for step_create —
  where `callee = address` so `Code callee = Code address` is
  consistent).
- `step_sstore_gas_consumption address key value` calls
  `access_slot (SK address key)` before the outer `write_storage
  address key value` executes. `access_slot` adds to
  `rollback.accesses.storageKeys`. Any slot modification is
  access-listed.
- Both `proceed_call` and `proceed_create` grow the context stack by
  **exactly 1**. Combined with handle_step popping by at most 1, this
  gives `step_length_change ∈ {-1, 0, +1}`.
- For step_call INL-grew: the address is NOT a precompile. This is
  because precompile "success" uses `finish` which returns INR NONE,
  so a precompile-succeeding proceed_call returns INR, not INL. INL
  return means the else-branch (`return ()`) fired, i.e. not a
  precompile. Simplifies the push-structure analysis.
- Invariant strengthening cascade is limited: 4 theorems need a new
  hypothesis; at the top level (single initial context) the new
  hypothesis reduces trivially to `outputTo_consistent es`.

## The claim

```hol
Theorem run_call_inv_step:
  ∀es s s' r.
    es.contexts ≠ [] ∧
    run_call_inv es s ∧
    LENGTH s.contexts ≥ LENGTH es.contexts ∧
    step s = (r, s') ⇒
    run_call_inv es s'
```

where `run_call_inv` is strengthened to include
`outputTo_consistent_stack s` (see Work item 1 below) and
`active_rollbacks` is extended to include one more saved-rollback entry
at es's depth (see Work item 1' below).

## High-level argument

Strip `txParams` with `step_preserves_txParams`. Remaining:

1. `outputTo_consistent_stack s'` (stronger; subsumes
   `outputTo_consistent s'`).
2. `EVERY (λrb. storage_slot_preserved rb es.rollback)
         (active_rollbacks ed s')` where `ed = LENGTH es.contexts`.

Case-split on step's length change (always in {-1, 0, +1}).

### Case 0 — length preserved (same-frame step)

`step_same_frame` gives `same_frame_rel s s'`:

- `TL s'.contexts = TL s.contexts`,
  `SND (HD s'.contexts) = SND (HD s.contexts)`,
  `(FST (HD s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams`.
  Hence `active_rollbacks ed s'`'s tail equals that of `s`, and the
  head position's `msgParams` is unchanged (so
  `outputTo_consistent_stack` transfers).
- Invariant on tail transfers pointwise.
- For the head entry: `storage_slot_preserved s'.rollback es.rollback`
  follows from input + accesses monotonicity + the **new sub-lemma**
  `step_preserves_non_accessed_storage` (Work item 3).

### Case +1 — push

`step_inst_inl_grew_is_call` tells us op ∈
{Call, CallCode, DelegateCall, StaticCall, Create, Create2}. We need
the **new structural lemma** `step_inl_grew_push_structure` (Work
item 4):

```
s'.contexts = (child_ctx, pushed_rb) :: s.contexts
(∀a. (lookup_account a s'.rollback.accounts).storage =
     (lookup_account a s.rollback.accounts).storage)
(∀a. (lookup_account a pushed_rb.accounts).storage =
     (lookup_account a s.rollback.accounts).storage)
toSet s.rollback.accesses.storageKeys ⊆
  toSet s'.rollback.accesses.storageKeys
∀a. child_ctx.msgParams.outputTo = Code a ⇒
     child_ctx.msgParams.callee = a
```

From these facts:
- `active_rollbacks ed s' = s'.rollback :: pushed_rb :: TL (active_rollbacks ed s)`.
- Tail invariant transfers unchanged.
- `storage_slot_preserved {pushed_rb, s'.rollback} es.rollback`
  follows from per-slot storage equality + access-set monotonicity +
  input invariant on `s.rollback`.
- `outputTo_consistent_stack s'`: old stack was consistent (input),
  new head is `child_ctx` which is outputTo-consistent.

### Case −1 — pop

Step's inner returned INR without pushing; handle_step popped one
frame. `pop_and_incorporate_context_{success,failure}_effect` +
`handle_step_pop_{success,failure}_memory_effect[_gen]` (all already
in `vfmHandleStep`) give:

- `s'.contexts = (new_head, SND (HD (TL s.contexts))) :: TL (TL s.contexts)`
  where `new_head.msgParams = (FST (HD (TL s.contexts))).msgParams`.
- Success pop (`e = NONE`): `s'.rollback = s.rollback`.
- Failure pop (`e ≠ NONE`): `s'.rollback = SND (HD s.contexts)`.

Consequences:
- Success pop: `s'.rollback = s.rollback` gives the head invariant
  directly. The new `active_rollbacks ed s'`'s tail is a sub-list of
  the old tail. Tail invariant transfers.
- Failure pop: `s'.rollback = SND (HD s.contexts)`. This is
  **already in `active_rollbacks (ed) s`** because we extended it
  to include the saved rollback at position `LENGTH s.contexts - ed`
  (which includes HD when s is at depth ed). So its
  `storage_slot_preserved` claim was already part of the input
  invariant.
- `outputTo_consistent_stack s'`: new head's msgParams = old
  position-1 msgParams, which was outputTo-consistent by input
  `outputTo_consistent_stack s`. Remaining tail is sub-list of old.

## Work items (in order)

### 1. Strengthen `run_call_inv` (~50 lines)

Add a per-context outputTo-consistency predicate:

```hol
Definition outputTo_consistent_ctx_def:
  outputTo_consistent_ctx c ⇔
    ∀a. c.msgParams.outputTo = Code a ⇒ c.msgParams.callee = a
End

Definition outputTo_consistent_stack_def:
  outputTo_consistent_stack s ⇔
    s.contexts ≠ [] ∧
    EVERY outputTo_consistent_ctx (MAP FST s.contexts)
End
```

Extend `active_rollbacks` to include one more saved-rollback entry
(the one at es's depth, so that pop-from-same-depth's restored
rollback is tracked):

```hol
Definition active_rollbacks_def:
  active_rollbacks ed s =
    s.rollback ::
    MAP SND (TAKE (LENGTH s.contexts - ed + 1) s.contexts)
End
```

Update `run_call_inv`:

```hol
Definition run_call_inv_def:
  run_call_inv es s ⇔
    s.txParams = es.txParams ∧
    outputTo_consistent_stack s ∧
    EVERY (λrb. storage_slot_preserved rb es.rollback)
          (active_rollbacks (LENGTH es.contexts) s)
End
```

Update:
- `run_call_inv_refl`: add hypotheses `outputTo_consistent_stack es`
  and `storage_slot_preserved (SND (HD es.contexts)) es.rollback`.
  (In practice this latter is `storage_slot_preserved es.rollback
  es.rollback` which is reflexivity, when `SND (HD es.contexts) =
  es.rollback` at run_call entry — a standard shape.)
- `run_call_preserves_inv`: add hypotheses.
- `run_call_preserves_storage_outside_accessed_slots`: add hypotheses.
- `run_call_preserves_txParams`: add hypothesis.

(The remaining `outputTo_consistent s` property is derivable from
`outputTo_consistent_stack s` if needed, via the first context's
consistency.)

### 2. Prove `step_length_change` (~30 lines)

```hol
Theorem step_length_change:
  ∀s r s'. step s = (r, s') ∧ s.contexts ≠ [] ⇒
    LENGTH s'.contexts = LENGTH s.contexts ∨
    LENGTH s'.contexts = LENGTH s.contexts + 1 ∨
    LENGTH s'.contexts + 1 = LENGTH s.contexts
```

**Strategy**: `step = handle inner handle_step`. Split on whether
inner returned INL or INR.

- If INL: `same_frame_or_grow_step_inner` + `proceed_*_length` gives
  length is preserved or exactly +1.
- If INR: inner's length change is 0 or +1 (same_frame_or_grow). Then
  handle_step may reraise (no change) or pop (−1). So total change is
  in {−1, 0, +1}. (In particular, +1 + (−1) = 0 is possible.)

### 3. Prove `step_preserves_non_accessed_storage` (~80 lines)

```hol
Theorem step_preserves_non_accessed_storage:
  step s = (r, s') ∧ s.contexts ≠ [] ⇒
  ∀a k. ¬fIN (SK a k) s'.rollback.accesses.storageKeys ⇒
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
```

**Strategy**: unfold step as `handle inner handle_step`.

- **The `handle_step` pop path** may set_rollback. But `set_rollback`
  replaces `s.rollback` with a saved one, which may have different
  storage. BUT the saved rollback's storage is ALWAYS equal to some
  prior state's storage (since storage only changes via SSTORE, and
  access-listing tracks those changes). Specifically: the pushed
  rollback's storage equals the state-at-push's storage, which
  propagates. This is more subtle than the inner case and requires
  the set_rollback to preserve the access-listed property.
  - Actually simpler: `set_rollback r` just sets rollback to `r`.
    The hypothesis is `¬fIN (SK a k) s'.rollback.accesses.storageKeys`,
    i.e., in the popped-to rollback `r`. Since `r` was a state pushed
    at some earlier point, and we assume the invariant holds there,
    we can't cleanly establish storage equality between `r` and `s`
    here — storage may have diverged in the popped-out frame!
  - **This is a genuine issue for Case 0** if it includes a pop path.
    But Case 0 specifically requires length PRESERVED. A pop from
    length n to n-1 is Case −1, not Case 0. Case 0 happens when:
    - Inner returns INL without grow (most opcodes).
    - Inner returns INR, handle_step reraises (n ≤ 1). This is the
      "root frame" case which requires `n = 1` contexts. Excluded
      by `LENGTH s.contexts ≥ LENGTH es.contexts ≥ 1` and the step
      not popping (otherwise length would shrink).
    - Inner grows by 1, handle_step pops by 1. This can happen! A
      CALL to a precompile that fails: inner returns INR with grow,
      handle_step pops. Net length: 0.

  So Case 0 CAN include the inner-grow-then-pop path. In that case
  set_rollback runs. `step_preserves_non_accessed_storage` needs to
  handle this.

  **Actually the fix is cleaner than expected**: in the inner-grow-
  then-pop path, the set_rollback restores the **pushed_rb** which
  equals `s.rollback` at the point of push (modulo access-address
  during step_call prefix, which doesn't change accounts). So after
  pop, `s'.rollback.accounts = s.rollback.accounts`. Storage
  preserved.

  **Caveat**: if transfer_value ran in proceed_call, the push captured
  `pushed_rb = (state entering proceed_call).rollback`, which has
  NO transfer_value applied. So `pushed_rb.accounts.storage =
  s.rollback.accounts.storage` (both pre-transfer, since transfer
  only touches balance). ✓

- **The inner no-grow case** (step_inst returned INL or INR without
  grow): use `cp_step_inst_non_call[simp]` to handle 60+ opcodes
  uniformly. For the 10 exceptions:
  - **Log n**: modifies `logs`, not accounts. Storage preserved.
  - **SelfDestruct**: `transfer_value` (balance-only), `add_to_delete`,
    `update_account` at callee with balance=0 (preserves storage via
    `transfer_value_preserves_storage` etc.).
  - **Call/CallCode/DelegateCall/StaticCall** without grow: either
    abort_call_value, abort_unuse (both psf, no account change), or
    proceed_call with grow (handled via pop case above).
  - **Create/Create2** without grow: abort_create_exists
    (`increment_nonce`, no storage change) or proceed_create with
    grow.
  - **TStore**: `write_transient_storage` modifies `tStorage`, not
    accounts. Storage preserved.
  - **SStore** (non-transient): `step_sstore_gas_consumption` calls
    `access_slot (SK address key)` adding to storageKeys, BEFORE
    `write_storage address key value`. Thus any modification at
    `(addr, k) = (address, key)` has `(SK addr k) ∈ s'.storageKeys`.
    Contrapositive: slots with `(SK a k) ∉ storageKeys` are
    unchanged.

### 4. Prove `step_inl_grew_push_structure` (~150 lines)

```hol
Theorem step_inl_grew_push_structure:
  step_inst op s = (INL (), s') ∧
  s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  ∃child_ctx pushed_rb.
    s'.contexts = (child_ctx, pushed_rb) :: s.contexts ∧
    (∀a. (lookup_account a s'.rollback.accounts).storage =
         (lookup_account a s.rollback.accounts).storage) ∧
    (∀a. (lookup_account a pushed_rb.accounts).storage =
         (lookup_account a s.rollback.accounts).storage) ∧
    toSet s.rollback.accesses.storageKeys ⊆
      toSet s'.rollback.accesses.storageKeys ∧
    (∀a. child_ctx.msgParams.outputTo = Code a ⇒
         child_ctx.msgParams.callee = a)
```

**Strategy**: case on op via `step_inst_inl_grew_is_call`.

- **Call family (4 cases)**: unfold step_call, peel psf prefix
  (no account/storage change, accesses monotonic). At proceed_call:
  get_rollback captures sp.rollback; transfer_value modifies balance
  only; push_context prepends `(child, sp.rollback) :: sp.contexts`
  where sp.contexts = s.contexts; dispatch_precompiles else-branch
  (return (), the only way to INL-return is address ∉ precompiles).
  Child has `outputTo = Memory mr` (satisfies outputTo_consistent_ctx
  vacuously).
- **Create family (2 cases)**: similar but push structure captured
  by proceed_create. Child has `outputTo = Code address = Code callee`
  (satisfies outputTo_consistent_ctx).

Both cases share a **template** that can likely be extracted into
a helper. Expect ~100 lines of actual novel content, ~50 lines of
case-scaffolding.

### 5. Assemble `run_call_inv_step` (~150 lines)

The main proof. Steps:

1. Strip `txParams` as today.
2. Prove `outputTo_consistent_stack s'` (needed by the invariant).
3. `step_length_change` → 3 cases.
4. **Case 0**: `step_same_frame` + `step_preserves_non_accessed_storage`
   + tail-equality + msgParams-equality + access monotonicity.
5. **Case +1**: `step_inl_grew_push_structure` + tail-extension + per-
   slot equality + new-child outputTo-consistency.
6. **Case −1**: `pop_and_incorporate_context_{success,failure}_effect`
   + tail-sublist + set_rollback-to-active-entry reasoning + msgParams
   of old position-1.

## Execution order and checkpoints

1. **Checkpoint A** (Work item 1 + 2):
   - Add `outputTo_consistent_stack`, strengthen `run_call_inv`,
     update the 4 cascading theorems (likely only hypothesis
     additions).
   - Prove `step_length_change`.
   - **Verify**: file builds. 1 cheat remaining (`run_call_inv_step`).
2. **Checkpoint B** (Work item 3):
   - Prove `step_preserves_non_accessed_storage`.
   - **Verify**: theorem proves on its own.
3. **Checkpoint C** (Work item 4):
   - Prove `step_inl_grew_push_structure`.
   - **Verify**: theorem proves on its own.
4. **Checkpoint D** (Work item 5):
   - Assemble `run_call_inv_step` using the three helpers.
   - **Verify**: cheat removed, full file builds clean.

## Revised size estimate

| Item | Lines |
|---|---|
| Invariant strengthening + active_rollbacks extension + cascade | 50 |
| `step_length_change` | 30 |
| `step_preserves_non_accessed_storage` | 80 |
| `step_inl_grew_push_structure` | 150 |
| `run_call_inv_step` main proof | 150 |
| **Total** | **~460** |

## Residual risks

- **Case 0's inner-grow-then-pop sub-case of `step_preserves_non_accessed_storage`**
  is subtler than a flat per-opcode case analysis. The set_rollback
  restores the pushed rollback whose storage equals (pre-transfer)
  `s.rollback.accounts.storage`. Verifying this cleanly may add
  20–30 lines.
- **Case −1's outputTo-consistency claim** relies on the popped-to
  msgParams being the old position-1 context's, which holds because
  msgParams is immutable.
- The `step_inl_grew_push_structure` lemma reuses the approach from
  `step_call_inr_grow_structure` (Cheat 1) but for 6 branches
  (Call/CallCode/DelegateCall/StaticCall/Create/Create2) instead of
  one aggregated proof. Template extraction should prevent duplication.
- The extended `active_rollbacks` requires `run_call_inv_refl` to
  establish `storage_slot_preserved (SND (HD es.contexts)) es.rollback`.
  For the standard entry shape `SND (HD es.contexts) = es.rollback`
  this is reflexivity. We may need to add this as an explicit
  hypothesis to the downstream theorems if callers don't provide
  the standard shape.
