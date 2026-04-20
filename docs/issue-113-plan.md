# Issue #113 — Preservation of storage (and more) outside a call frame

**Tracking:** <https://github.com/verifereum/verifereum/issues/113>

## Statement of the problem

While a call is running — that is, while the call stack `st.contexts` has
depth ≥ the depth at the call's entry — the only storage that may be
written is the called account's.

The issue mentions porting `run_call_def` from
`vyper-hol/lowering/e2eCorrectnessScript.sml` and introducing a "current
call" variant (no child call descended into) that is related to the full
`run_call`.

## Approach in outline

Rather than proving storage preservation in isolation, we build a single
reusable framework that captures *everything* provably invariant across an
EVM step that does not push or pop a context. From that single "same-frame"
relation we derive, by transitive composition, preservation theorems for
three progressively larger scopes:

1. `run_within_frame` — iterated `step` so long as the stack depth is
   exactly the starting depth (no push has happened and no pop has
   happened).
2. `run_call` — iterated `step` so long as the stack depth is ≥ the
   starting depth (the current call and its descendants).
3. `run` — the whole transaction (already defined).

The storage-preservation theorem requested by the issue is a direct
corollary, and we additionally get a raft of other useful invariants (tx
parameters, non-head context immutability, log-monotonicity, gas
monotonicity, access-list monotonicity, etc.) from the same framework with
no extra work.

## Files and artefacts

### 1. Additions to `spec/vfmExecutionScript.sml`

Placed next to `run_def`. These declare `run_call` and `run_within_frame`
as first-class semantic concepts of the EVM: the former executes the
current call and any children until control returns past the starting
depth; the latter executes within the current frame only, stopping as
soon as a child is pushed or the frame is popped.

```hol
Definition run_call_def:
  run_call es =
    OWHILE (λ(r, s). ISL r ∧ LENGTH s.contexts ≥ LENGTH es.contexts)
           (step o SND) (INL (), es)
End

Definition run_within_frame_def:
  run_within_frame es =
    OWHILE (λ(r, s). ISL r ∧ LENGTH s.contexts = LENGTH es.contexts)
           (step o SND) (INL (), es)
End
```

**Status:** complete (merged).

### 2. New theory `spec/prop/vfmCallFrameScript.sml`

Ancestors: `vfmExecution`, `vfmExecutionProp`, `vfmStaticCalls`,
`vfmTxParams`, `vfmDomainSeparation` (and `rich_list` for `IS_PREFIX`).

Contents:

- Helper predicate `msdomain_compatible` capturing the two allowed
  transitions for `msdomain`: `Enforce d` stays equal, `Collect d`
  grows under `subdomain`. **Status: complete.**
- Helper predicate `callee_local_changes callee r r'` capturing the
  permitted changes to a `rollback_state` within one frame: at
  non-callee accounts, the storage, code, and nonce must match; the
  balance is free (SELFDESTRUCT transfers balances to arbitrary
  addresses). tStorage must match at non-callee addresses. At the
  callee, only the nonce monotonicity is claimed. **Status: complete.**
- The omnibus relation `same_frame_rel` built on top of those helpers.
  **Status: complete.**
- Reflexivity, transitivity (plus refl/trans for the two helpers).
  **Status: complete.**
- `preserves_same_frame m` — a monadic same-frame preservation
  predicate with the standard composition lemmas (bind, ignore_bind,
  handle, cond, case_*, let, uncurry). Replaces the originally
  planned "`cp ⇒ same_frame_rel` bridge": `cp` is not strong enough
  on its own (it does not preserve `txParams`, accesses, msdomain, or
  refunds), so we build a purpose-built predicate. **Status: complete.**
- Primitive-level `preserves_same_frame` lemmas for every monadic
  primitive (getters, head-context writers, rollback writers,
  access/domain writers, parameterised `set_current_context`), plus
  pointwise companions (`write_storage_same_frame` etc.) for use in
  larger opcode proofs. **Status: complete.**
- Compound-helper `preserves_same_frame` lemmas for every `step_*`
  intermediate and all 18 precompiles. **Status: complete.**
- Per-opcode `preserves_same_frame (step_inst op)[simp]` for every
  Group-1 opcode (77 theorems, including SSTORE, TSTORE, and
  SELFDESTRUCT). **Status: complete.**
- `psf p m` — a state-indexed same-frame preservation predicate used
  for opcodes whose proofs need to thread value-level facts from
  getter-binds through to later writes. Mirrors
  `ignores_extra_domain_pred` from `vfmDomainSeparation`. Includes a
  bridge `psf (λs. T) m ⇔ preserves_same_frame m` so the primitive
  lemmas auto-lift. **Status: complete.**
- Handle-layer lemmas (`outputTo_consistent`, `psf_handle_create`,
  `handle_exception_same_frame`, `handle_step_same_frame`) under the
  length-preservation hypothesis. **Status: complete.**
- `step_same_frame`: the lift from primitives to the full `step`, by
  opcode case analysis.
- `run_within_frame_preserves`: an OWHILE induction that closes the
  frame under transitivity. (The definition of `run_within_frame` lives
  in `vfmExecution`.)
- Exported named corollaries (see below).

### 3. New theory `spec/prop/vfmRunCallScript.sml`

Ancestors: `vfmExecution`, `vfmExecutionProp`, `vfmCallFrame`.

**Status: skeleton built; 1 cheat (`run_call_inv_step`).**

Contents:

- `active_rollbacks_def`: the list of rollbacks we could revert to
  from a descendant state `s` of `es` — `s.rollback` plus every saved
  rollback in contexts pushed on top of `es`'s depth.
- `storage_slot_preserved_def`: per-slot predicate on two rollback
  states saying storage at `(a, k)` agrees outside of `storageKeys`.
  Matches `access_slot`'s granularity exactly.
- `run_call_inv_def`: the 2-state invariant between the initial `es`
  and any descendant `s`. Asserts `s.txParams = es.txParams`
  plus `EVERY (λrb. storage_slot_preserved rb es.rollback)
  (active_rollbacks ...)`.
- `run_call_inv_refl` — reflexivity for the initial state. **Proven**.
- `run_call_inv_step` — single-step preservation. **Currently cheated.**
  Structural outline documented in proof comment (4-case analysis
  on step's length effect).
- `run_call_preserves_inv` — lift to whole `run_call` via
  `OWHILE_INV_IND`. **Proven** (modulo cheat in
  `run_call_inv_step`).
- `run_call_preserves_storage_outside_accessed_slots` — the headline
  theorem. **Proven** via `run_call_preserves_inv`.
- `run_call_preserves_txParams` — companion. **Proven**.
- `storage_slot_preserved_refl`, `storage_slot_preserved_trans_mono`,
  `storage_slot_preserved_compose` — helper lemmas. **Proven**.

Companion theorems still to add (all simple corollaries of
`run_call_preserves_inv` once the invariant is strengthened):

- `run_call_preserves_tStorage_outside_accessed`
- `run_call_preserves_code_outside_accessed`
- `run_call_preserves_balance_outside_accessed`
- `run_call_accesses_grow`, `run_call_logs_grow`, `run_call_gas_monotone`,
  `run_call_refund_monotone`, `run_call_domain_compatible`
- `run_call_preserves_nonhead_contexts`, `run_call_preserves_head_msgParams`

`run_call_tr` tail-recursive form / `run_call_eq_tr` / cross-boundary
step lemmas: **not needed** for the current invariant approach.
Deferred. (`OWHILE_INV_IND` over `run_call_def` directly is
sufficient.)

## The `same_frame_rel` relation

As built in `vfmCallFrameScript`:

```hol
Definition callee_local_changes_def:
  callee_local_changes callee r r' ⇔
    (∀a. a ≠ callee ⇒
         (lookup_account a r'.accounts).storage =
         (lookup_account a r.accounts).storage ∧
         (lookup_account a r'.accounts).code =
         (lookup_account a r.accounts).code ∧
         (lookup_account a r'.accounts).nonce =
         (lookup_account a r.accounts).nonce) ∧
    (∀a. a ≠ callee ⇒ r'.tStorage a = r.tStorage a) ∧
    (lookup_account callee r.accounts).nonce ≤
      (lookup_account callee r'.accounts).nonce
End

Definition msdomain_compatible_def:
  msdomain_compatible m1 m2 ⇔
    case (m1, m2) of
    | (Enforce d1, Enforce d2) => d1 = d2
    | (Collect d1, Collect d2) => subdomain d1 d2
    | _ => F
End

Definition same_frame_rel_def:
  same_frame_rel s s' ⇔
    s.contexts ≠ [] ∧
    LENGTH s'.contexts = LENGTH s.contexts ∧
    TL s'.contexts = TL s.contexts ∧
    SND (HD s'.contexts) = SND (HD s.contexts) ∧
    (FST (HD s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams ∧
    s'.txParams = s.txParams ∧
    callee_local_changes
      (FST (HD s.contexts)).msgParams.callee
      s.rollback s'.rollback ∧
    toSet s.rollback.accesses.addresses ⊆
      toSet s'.rollback.accesses.addresses ∧
    toSet s.rollback.accesses.storageKeys ⊆
      toSet s'.rollback.accesses.storageKeys ∧
    msdomain_compatible s.msdomain s'.msdomain ∧
    IS_PREFIX (FST (HD s'.contexts)).logs (FST (HD s.contexts)).logs ∧
    (FST (HD s.contexts)).addRefund ≤ (FST (HD s'.contexts)).addRefund ∧
    (FST (HD s.contexts)).subRefund ≤ (FST (HD s'.contexts)).subRefund
End
```

Quantities that are **deliberately free** in this relation, because they
do change during a frame:

- The head context's `stack`, `memory`, `pc`, `jumpDest`, `returnData`.
- The callee account's `storage`, `code`, and `nonce`.
- The callee slot's transient storage.
- The head context's `gasUsed` (see note below).
- The **balance** of any account, callee or otherwise (SELFDESTRUCT can
  transfer the callee's balance to an arbitrary beneficiary; CALL with
  positive value transfers between two addresses).
- The rollback's `toDelete` list (SELFDESTRUCT appends its sender).

The last two entries have corollaries later that recover preservation
under additional hypotheses (see the access-list-based corollaries
below).

Code is listed as free because when a CREATE'd frame finishes
successfully, `handle_create` installs the returned bytecode at the
callee's address. This is the only way any account's `code` can change
during a step. Non-callee accounts have their entire account record
preserved, so in particular their code is unchanged — which is the
property users typically need ("my deployed contract's code is stable
").


### Why `gasUsed` is not in `same_frame_rel`

At the full-`step` level, head `gasUsed` is monotone (in fact strictly
increasing on success) — this is the content of
`decreases_gas_cred T 0 0 step` in `vfmDecreasesGasScript`. However, at
the sub-step level, the primitive `unuse_gas n` decreases `gasUsed`, and
it is `cp`. To keep the `cp ⇒ same_frame_rel` bridge lemma clean (no
"except when…" caveats), gas monotonicity is proved separately and
lifted to `run_within_frame` as its own corollary:

- `step_same_frame_gas_monotone`: if `step s = (r, s')` and
  `same_frame_rel s s'` holds (so length and `TL` are preserved and
  `gasLimit` of the head is unchanged), then
  `head(s).gasUsed ≤ head(s').gasUsed`. Proved from
  `decreases_gas_cred_step` by unfolding `contexts_weight` /
  `unused_gas`, using that only the head's contribution can move.
- `run_within_frame_gas_monotone`: iterated version by OWHILE induction.

Refund counters `addRefund` and `subRefund` *are* monotone under every
`cp` operation (no primitive decreases them), so they stay in
`same_frame_rel`.

## Audit: why `same_frame_rel` holds at every step whose length is preserved

Summary of case analysis over `step`:

- **`cp`-proved opcodes** (arithmetic, stack, memory, context and msgParams
  reads, JUMP/PC/MSIZE/GAS/PUSH/DUP/SWAP, BALANCE, EXTCODE*, KECCAK256,
  CALL_DATA*, COPY_TO_MEMORY family, RETURN_DATA_COPY, BLOCK_HASH,
  BLOB_HASH, SELF_BALANCE, and the pure-compute precompile dispatch):
  `cp` implies `same_frame_rel` via a bridge lemma.
- **SLOAD / TLOAD**: `cp` + grows `accesses`. Bridge lemma suffices.
- **SSTORE** (non-transient): `access_slot` grows `accesses.storageKeys`,
  `consume_gas`, `update_gas_refund`, `assert_not_static`,
  `write_storage callee k v`. Only callee's storage moves; everything else
  covered by bridge or by dedicated `write_storage` lemma.
- **TSTORE**: `write_transient_storage callee k v`. Only callee's
  `tStorage` slot moves.
- **LOG n**: `push_logs ls` appends to head logs — covered by the
  `IS_PREFIX` conjunct.
- **CALL family, abort path** (`abort_call_value`, `abort_unuse`):
  `consume_gas`, `access_address`, stack/mem reads, `unuse_gas stipend`
  (net gas monotone over the step), stack push, `inc_pc`. No account
  modifications. `cp`-reducible.
- **CALL family, non-abort**: pushes context → length changes → out of
  scope.
- **CREATE family, abort via `abort_unuse`**: `consume_gas`,
  `access_address`, `ensure_storage_in_domain`, `unuse_gas cappedGas`
  (net zero over step). No account modifications. `cp`-reducible.
- **CREATE family, abort via `abort_create_exists`**:
  `update_accounts $ increment_nonce senderAddress` where
  `senderAddress = get_callee`. Only callee's nonce moves; `same_frame_rel`
  permits this (nonce is free for callee, bound by monotonicity).
- **CREATE family, non-abort**: pushes context → length changes → out of
  scope.
- **Stop / Return / Revert / Invalid / OOG / non-outermost handled error**:
  pop frame via `handle_step` → length changes → out of scope.
- **SELFDESTRUCT**: `step_inst SelfDestruct` transfers balance to the
  beneficiary and may append to `toDelete`, then `finish`es. The
  length-change happens in `handle_step` (possibly via pop, or via
  outermost reraise when `n ≤ 1`). The `same_frame_rel` conjuncts
  remaining after weakening (storage, code, nonce, tStorage at
  non-callees; callee nonce monotone; msgParams; accesses-grow; logs;
  refunds) are all preserved. Balance and `toDelete` are deliberately
  not claimed.
- **Outermost-frame error** (`handle_exception` with `n ≤ 1`, reraises):
  length unchanged. Effect: head `gasUsed` may rise (by `gasLeft`), head
  `returnData` may be cleared. Both free in `same_frame_rel`. ✓
- **`vfm_abort` error**: `handle_step` reraises immediately; state
  unchanged. Reflexivity of `same_frame_rel`. ✓
- **`handle_create` install-code branch** (`e = NONE` and
  `outputTo = Code address`): `update_accounts` writes
  `address`'s `code` field. Here `address` is the callee of the
  current (CREATE'd) head frame, so this is a change to the callee's
  `code`. `same_frame_rel` leaves callee `code` free, so the conjunct
  holds. Non-callee accounts are unaffected. ✓

### SELFDESTRUCT and why balance / toDelete are dropped

`step_inst SelfDestruct` transfers the callee's balance to an arbitrary
beneficiary and may append to `toDelete`. These effects occur whether
or not the frame is popped in the same `step` (the pop happens in
`handle_step`, after the transfer). Including "balance equal at
non-callees" or "`toDelete` equal" in `same_frame_rel` would make the
relation unprovable for the SELFDESTRUCT path.

We considered adding an anti-SELFDESTRUCT precondition to every
theorem, but for interactive contracts (those that make external
CALLs) discharging "no SELFDESTRUCT anywhere in the call tree's code"
is impractical. Instead, the relation is weakened so all theorems
apply uniformly, with or without SELFDESTRUCT.

Users who need balance preservation can derive it as a corollary:
because SELFDESTRUCT calls `access_address` on the beneficiary before
transferring, the beneficiary is in `rollback.accesses.addresses`.
Likewise, `transfer_value` call-sites in `proceed_call` have access-
listed both endpoints. So the balance of any address not in the final
`accesses.addresses` is preserved. A separate corollary
`run_within_frame_preserves_balance_outside_accessed` (and similar for
`run_call`) captures this and lives as a follow-up to the main
framework.

## Key derived theorems

### Within-frame (in `vfmCallFrameScript`)

```
Theorem run_within_frame_preserves:
  es.contexts ≠ [] ∧ run_within_frame es = SOME (r, es') ⇒
  same_frame_rel es es'
```

Named exported corollaries:

- `run_within_frame_preserves_txParams`
- `run_within_frame_preserves_storage_outside_callee`
- `run_within_frame_preserves_tStorage_outside_callee`
- `run_within_frame_preserves_code_outside_callee`
- `run_within_frame_preserves_nonce_outside_callee`
- `run_within_frame_preserves_nonhead_contexts`
- `run_within_frame_preserves_head_msgParams`
- `run_within_frame_preserves_saved_rollback`
- `run_within_frame_callee_nonce_monotone`
- `run_within_frame_logs_grow`
- `run_within_frame_accesses_grow`
- `run_within_frame_gas_monotone`
- `run_within_frame_refund_monotone`
- `run_within_frame_domain_compatible`

Additional follow-up corollaries (outside the main chain, recovering
the dropped guarantees under access-list hypotheses):

- `run_within_frame_preserves_balance_outside_accessed`
- `run_within_frame_toDelete_grows` (and symmetrically, the added
  addresses are all access-listed by the SELFDESTRUCT step that added
  them).

### Across a whole call (in `vfmRunCallScript`)

The headline theorem matching the issue:

```
Theorem run_call_preserves_storage_outside_accessed:
  run_call es = SOME (r, es') ⇒
  ∀a. a ∉ es'.rollback.accesses.addresses ⇒
      (lookup_account a es'.rollback.accounts).storage =
      (lookup_account a es.rollback.accounts).storage
```

Its per-slot strengthening:

```
Theorem run_call_preserves_storage_outside_accessed_slots:
  run_call es = SOME (r, es') ⇒
  ∀a k. SK a k ∉ es'.rollback.accesses.storageKeys ⇒
      lookup_storage k (lookup_account a es'.rollback.accounts).storage =
      lookup_storage k (lookup_account a es.rollback.accounts).storage
```

Both hold uniformly whether the call succeeded or reverted, because on
revert `rollback.accesses` is rolled back in lockstep with
`rollback.accounts`.

Companion theorems (for free from the same framework):

- `run_call_preserves_txParams`
- `run_call_preserves_tStorage_outside_accessed`
- `run_call_preserves_balance_outside_accessed`
- `run_call_preserves_code_outside_accessed` (stronger: only
  newly-created-contract addresses can have code installed, via the
  `handle_create` branch; followup if useful)
- `run_call_preserves_nonhead_contexts` (contexts below the starting
  depth are byte-for-byte unchanged)
- `run_call_preserves_head_msgParams`
- `run_call_accesses_grow`, `run_call_logs_grow`,
  `run_call_gas_monotone`, `run_call_refund_monotone`,
  `run_call_domain_compatible`

## What is reused from existing theories (no modifications required)

- `vfmStaticCallsScript`: `cp`, `ctx_pres`, all their composition and
  leaf lemmas. The `cp ⇒ same_frame_rel` bridge means the heavy lifting
  of per-primitive classification is already done.
- `vfmTxParamsScript`: `step_preserves_txParams` is used in the proof of
  `step_same_frame` (txParams conjunct) and at push/pop boundaries.
- `vfmDecreasesGasScript`: `run_tr_def`, `run_tr_ind`, `run_eq_tr`, and
  the gas-termination recipe — reused directly for `run_call_tr`. Also
  `decreases_gas_cred_step` is used in the gas-monotone corollary.
- `vfmDomainSeparationScript`: `subdomain`, `domain_compatible`, with
  their reflexivity and transitivity lemmas.
- `vfmExecutionPropScript`: the `_preserves_nonempty_contexts` family.

No existing file is deleted or rewritten.

## Remaining design choices and non-goals

- **Per-slot vs. per-address.** We prove both; the per-slot version is
  the primary statement because it is strictly stronger and closer to the
  usage in contract proofs.
- **Closed-form `run_call` decomposition** (`run_call = run_within_frame
  ; (if pushed then run_call recursively) ; run_call`) is *not* required
  to derive the headline theorems. It is a nice-to-have for downstream
  users. Deferred.
- **Initial-state hypothesis variants.** Statements with `a ∉
  es.rollback.accesses.addresses` in the hypothesis follow from the
  final-state version by monotonicity; we expose them as corollaries.
- **SELFDESTRUCT within `same_frame_rel`.** Covered. The relation is
  deliberately weak enough (balance and `toDelete` free) that
  SELFDESTRUCT's effects satisfy it. Addresses in SELFDESTRUCT's
  transfer are access-listed, so follow-up balance-preservation
  corollaries can exclude them.
- **`code` mutation semantics.** Code can be installed at the callee's
  address via `handle_create` during the frame where the CREATE'd
  context is being deployed. `same_frame_rel` accepts this by leaving
  callee `code` free. Non-callee code is preserved (it is part of the
  full-account-equality conjunct for non-callees). A tighter
  `run_call_preserves_code_outside_newly_created` theorem is a
  candidate follow-up.

## Ordered work plan

1. [x] Add `run_call_def` and `run_within_frame_def` to
   `vfmExecutionScript.sml`, rebuild `spec/`.
2. Build `spec/prop/vfmCallFrameScript.sml`:
   a. [x] Define helpers (`msdomain_compatible`, `callee_local_changes`)
      and `same_frame_rel`; prove reflexivity and transitivity.
      Required a weakening of `callee_local_changes` to permit
      SELFDESTRUCT (balance at non-callees is free; `toDelete` is
      dropped from `same_frame_rel`).
   b. [x] Define `preserves_same_frame` (monadic same-frame property)
      with composition lemmas (bind, ignore_bind, handle, cond,
      case_*, let, uncurry).
   c. [x] Primitive-level `preserves_same_frame` leaves: getters,
      head-context writers, rollback writers (`write_storage`,
      `write_transient_storage`, `update_accounts (increment_nonce)`
      at the callee), access/domain ops, plus a parameterised
      `set_current_context` lemma. Plus pointwise companions
      `write_storage_same_frame` etc. for use inside larger opcode
      proofs.
   d. [x] Compound-helper `preserves_same_frame` lemmas for every
      `step_*` intermediate (arithmetic helpers, step_sload,
      step_sstore_gas_consumption, copy_to_memory, memory and control
      helpers, all 18 precompiles, dispatch_precompiles, abort
      helpers, inc_pc_or_jump).
   e. [x] Per-opcode `preserves_same_frame (step_inst op)[simp]` for
      every Group-1 opcode (77 theorems covering everything except
      Call, CallCode, DelegateCall, StaticCall, Create, Create2, and
      SelfDestruct).
   f. [x] `psf` state-indexed framework (composition rules, bridges
      to and from `preserves_same_frame`, specialised getter-binds
      for `get_callee`, `get_current_context`, `get_caller`,
      `get_value`, `get_accounts`, `get_tStorage`, `get_rollback`,
      `get_tx_params`, `get_original`, pointwise rollback-writer
      lemmas, transfer helpers).
   g. [x] `preserves_same_frame_step_sstore` via the `psf` framework.
   h. [x] Handle-layer lemmas: `outputTo_consistent`,
      `psf_handle_create`, `handle_exception_same_frame`,
      `handle_step_same_frame`.
   i. [x] `preserves_same_frame (step_inst SelfDestruct)` via new
      primitives (`psf_update_accounts_transfer_value`,
      `psf_add_to_delete`, `psf_update_accounts_callee_balance_only`)
      plus the `transfer_value_preserves_{storage,code,nonce}` field
      lemmas.
   j. [x] `proceed_call_length`, `proceed_create_length` — helpers
      showing the push always increases context length.
   k. [x] `same_frame_bind_preserves` — state-level bind-composition
      helper for the CALL/CREATE proofs.
   l. [x] `step_call_same_frame` and `step_create_same_frame` —
      PROVEN.
   m. [x] `step_same_frame` — PROVEN (with length-preservation
      hypothesis). The cross-frame cases
      `step_call_handle_step_inr_grow_same_frame` and
      `step_create_inr_no_grow` are used; both have remaining
      internal cheats documented below.
   n. [x] `run_within_frame_preserves` — PROVEN with the
      conditional invariant `(LENGTH s.contexts = LENGTH es.contexts
      ⇒ same_frame_rel es s)`.
   o. [x] `run_within_frame_gas_monotone` — PROVEN with same
      conditional invariant pattern.
   p. [x] Named `run_within_frame_*` corollaries exported (13).
3. [x] Create `spec/prop/vfmRunCallScript.sml`:
   a. [x] Define `active_rollbacks`, `storage_slot_preserved`,
      `run_call_inv` (2-state invariant with saved-rollback chain).
   b. [x] Prove `run_call_inv_refl`.
   c. [cheat] Prove `run_call_inv_step` (single-step preservation).
      Structural outline present; full proof sketched in-place.
   d. [x] Prove `run_call_preserves_inv` via `OWHILE_INV_IND`.
   e. [x] Export `run_call_preserves_storage_outside_accessed_slots`
      (the headline theorem) and `run_call_preserves_txParams`.
   f. **Deferred:** remaining companion corollaries (tStorage,
      code, balance, accesses, logs, gas, refund, domain, nonhead
      contexts, head msgParams). All follow from extending the
      invariant in the same pattern.

   `run_call_tr` / `run_call_eq_tr` / cross-boundary step lemmas
   are NOT needed for this approach. Deferred.
4. [x] `spec/prop/Holmakefile` — no changes required.

## Cheats discharged since plan was drafted

### Phase 1 flaws resolved

1. **“`same_frame_or_grow step`”** — FALSE claim removed.
   Reformulated `run_within_frame_preserves` and
   `run_within_frame_gas_monotone` using the conditional invariant
   `(LENGTH s.contexts = LENGTH es.contexts ⇒ same_frame_rel es s)`.

2. **Address-level headline** reformulated as the per-slot
   `run_call_preserves_storage_outside_accessed_slots` using
   `storageKeys`, not `addresses`. This matches `access_slot` exactly.

### Discharged cheats (across all sessions)

- `step_inst_inl_grew_is_call`
- `step_inst_inr_grew_is_call_family`
- `proceed_create_returns_inl`
- `run_within_frame_preserves`
- `run_within_frame_gas_monotone`
- `pop_and_incorporate_context_failure_effect`
- `handle_exception_pop_failure_memory_effect`
- `handle_step_pop_memory_effect`
- `step_create_inr_no_grow` (reduced to `step_create_grown_returns_inl`)
- Two msdomain / txParams / `e ≠ NONE` inner cheats inside
  `step_call_handle_step_inr_grow_same_frame`

### New helper lemmas (proven)

- `handle_exception_pop_success_memory_effect` and
  `handle_step_pop_success_memory_effect`: effect lemmas for the
  e = NONE path (precompile success).
- `SND_handle_step_msdomain` and 15 supporting `SND_*_msdomain`
  lemmas: handle_step does not modify msdomain at all.
- `abort_unuse_length`, `abort_create_exists_length`: both preserve
  context length.
- Strengthened `step_call_inr_grow_structure` conclusion to include
  `s1.rollback = sp.rollback` and `s1.msdomain = sp.msdomain`.

## Remaining cheats (5)

### `vfmCallFrameScript.sml` (4)

1. **`step_create_grown_returns_inl`** (≈ line 3045). Helper for the
   already-discharged `step_create_inr_no_grow`. States: if
   `step_create two s` grows contexts, its result is INL. Provable
   by structural analysis: prefix primitives preserve length;
   final if-branches are abort_unuse (length preserved, #3 helper),
   abort_create_exists (length preserved, #4 helper), or
   proceed_create (grows +1 and returns INL,
   `proceed_create_returns_inl`). Attempted `psf_or_inl_grow`
   predicate framework but composition through `bind` doesn't work
   cleanly when g grows+INL threaded into f that may return INR.
   A specialised framework that splits prefix (preserves_same_frame)
   from final branch would work.

2. **`step_call_inr_grow_structure`** (≈ line 3450). The biggest.
   Walk through step_call + proceed_call, identifying the
   intermediate state `sp` just before `push_context`. Establishes:
   - `¬ vfm_abort e`
   - `same_frame_rel s sp`
   - `s1.rollback = sp.rollback`, `s1.msdomain = sp.msdomain`
   - `s1.contexts = (callee_ctx, sp.rollback) :: (parent_ctx, old
     SND) :: TL sp.contexts`
   - parent_ctx preserves msgParams/logs/addRefund/subRefund
   - `callee_ctx.msgParams.outputTo = Memory mr`

   Requires careful structural unfolding of step_call's monad
   chain; estimate ~300 lines. Precompile failures are always
   `OutOfGas` / `InvalidParameter` / `KZGProofError`, never
   `vfm_abort` (verified by inspection of all 18 precompile
   definitions).

3. **Two `q = INL ()` subcheats** (≈ lines 3555, 3585) inside
   `step_call_handle_step_inr_grow_same_frame`. One in the e = NONE
   branch, one in the e ≠ NONE branch. Both assert: when
   `handle_step` pops the callee frame (length drops by 1), the
   result is INL.

   **Why not trivially true:** `handle_step`'s pop path runs
   `pop_and_incorporate_context`, which calls `unuse_gas` (may fail
   `Impossible`) and, in the Memory case, `push_stack` (may fail
   `StackOverflow`). Both INR paths leave state with length already
   dropped to `LENGTH s.contexts`, matching the theorem hypothesis.

   **What's needed to discharge:** either add a well-formedness
   hypothesis (`callee.gasUsed ≤ callee.msgParams.gasLimit` and
   `LENGTH (FST parent).stack < 1024`) threaded from prior
   invariants, OR strengthen the theorem conclusion to hold even
   when q = INR (state structure is still related to `s` via
   `same_frame_rel` because the partial finalization doesn't
   change msdomain/txParams/non-head-contexts/rollback).

### `vfmRunCallScript.sml` (1)

4. **`run_call_inv_step`** (≈ line 188). Four-case proof on step's
   length effect (see sketch in proof comment):
   a. Length preserved: `step_same_frame` + slot preservation on
      `same_frame_rel`.
   b. Length +1 (push): new saved rollback entry is s.rollback
      (pre-step), which was already active.
   c. Length −1 (pop success): active_rollbacks shrinks by one;
      `s'.rollback = s.rollback` preserved.
   d. Length −1 (pop revert): `s'.rollback = SND (HD s.contexts)`,
      which was the second entry of old `active_rollbacks`.

   Depends on: helper lemma characterising step's length change
   (±1 or 0); outputTo_consistent threading through run_call;
   step_same_frame for case (a); `step_call_handle_step_inr_grow_
   same_frame` (cheat #3) for case (c), push structure for (b).

## Net status

From 11 cheats at start to **5 cheats** now. Both plan flaws resolved.
Headline theorem `run_call_preserves_storage_outside_accessed_slots`
and `run_call_preserves_txParams` proven, modulo the 5 remaining
state-level / structural cheats.

Both files build with `holmake` in ~40 seconds, reporting CHEATED.
All remaining cheats have detailed proof sketches in-place.

### Summary of cheat dependency structure

```
run_call_preserves_storage_outside_accessed_slots (PROVEN)
  └─ run_call_preserves_inv (PROVEN)
       └─ run_call_inv_step             [CHEAT #4]

step_same_frame (PROVEN, used in cheat #4 case (a))
  └─ step_call_same_frame (PROVEN)
  └─ step_create_same_frame (PROVEN)

step_call_handle_step_inr_grow_same_frame     [2 inner CHEATS #3]
  ├─ step_call_inr_grow_structure            [CHEAT #2]
  ├─ handle_step_pop_memory_effect (PROVEN)
  └─ handle_step_pop_success_memory_effect (PROVEN)

step_create_inr_no_grow (PROVEN)
  └─ step_create_grown_returns_inl          [CHEAT #1]
```

### Archived audit notes

**Both audit adjustments have been applied** (see "Phase 1 flaws
resolved" above):

1. `same_frame_or_grow step` was FALSE; replaced with conditional
   invariant `(LENGTH s.contexts = LENGTH es.contexts ⇒ same_frame_rel
   es s)` inside `run_within_frame_preserves` and
   `run_within_frame_gas_monotone`. Both proven.
2. Address-level storage theorem was false as stated (SSTORE
   access-lists via `storageKeys`, not `addresses`). Replaced with
   the per-slot `run_call_preserves_storage_outside_accessed_slots`
   as the primary headline.

## Deferred follow-ups (outside #113 scope)

- Balance-outside-accessed corollary for `run_within_frame` and
  `run_call`, using access-list monotonicity to recover balance
  preservation that was dropped from `same_frame_rel` for SELFDESTRUCT.
- `toDelete`-grows-monotonically corollary.
- A tighter `run_call_preserves_code_outside_newly_created` theorem
  using CREATE-frame tracking.
