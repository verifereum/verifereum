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

### 1. Addition to `spec/vfmExecutionScript.sml`

Placed next to `run_def`. This declares `run_call` as a first-class semantic
concept of the EVM.

```hol
Definition run_call_def:
  run_call es =
    OWHILE (λ(r, s). ISL r ∧ LENGTH s.contexts ≥ LENGTH es.contexts)
           (step o SND) (INL (), es)
End
```

### 2. New theory `spec/prop/vfmCallFrameScript.sml`

Ancestors: `vfmExecution`, `vfmExecutionProp`, `vfmStaticCalls`,
`vfmTxParams`, `vfmDomainSeparation`, `vfmDecreasesGas`.

Contents:

- The omnibus relation `same_frame_rel`.
- Reflexivity, transitivity.
- `cp m ⇒ ∀s r s'. m s = (r, s') ∧ s.contexts ≠ [] ⇒ same_frame_rel s s'`
  — reuses every `cp` leaf lemma from `vfmStaticCalls`.
- Primitive-level lemmas for the non-`cp` writers:
  `write_storage`, `write_transient_storage`, `push_logs`,
  `update_gas_refund`, `access_slot`, `access_address`,
  `ensure_storage_in_domain`, `consume_gas`, `unuse_gas`, and the handful
  of `update_accounts` side-conditions we need for abort paths.
- `step_same_frame`: the lift from primitives to the full `step`, by
  opcode case analysis.
- `run_within_frame_def` and `run_within_frame_preserves`: an OWHILE
  induction that closes the frame under transitivity.
- Exported named corollaries (see below).

### 3. New theory `spec/prop/vfmRunCallScript.sml`

Ancestors: `vfmExecution`, `vfmCallFrame`, `vfmDecreasesGas`.

Contents:

- `run_call_tr_def` tail-recursive form, terminating by the same gas
  argument used for `run_tr` but additionally conditioned on
  `LENGTH contexts ≥ depth`.
- `run_call_eq_tr`: the equation connecting `run_call` to `run_call_tr`
  (mirrors `run_eq_tr`).
- Cross-boundary step lemmas:
  - `step_pushes` — describes what `step` does when
    `LENGTH s'.contexts = LENGTH s.contexts + 1` (CALL/CREATE success).
  - `step_pops`  — describes what `step` does when
    `LENGTH s'.contexts < LENGTH s.contexts` (Stop/Return/Revert/
    Invalid/OOG/SELFDESTRUCT).
- `run_call` preservation theorems stated using the existing
  `rollback.accesses.addresses` and `rollback.accesses.storageKeys` sets
  as the "touched" witness — no new bookkeeping is added to the
  execution state.
- Revert-aware corollaries: on a reverted child, `rollback.accesses` is
  restored along with the rest of `rollback`, so the uniform statement
  "storage at any address not in the final `accesses.addresses` is
  unchanged" holds in both the success and revert branches.

Decomposition / induction-principle theorems connecting `run_call` to
`run_within_frame` are *not* required for the issue and are deferred.

## The `same_frame_rel` relation

```hol
Definition same_frame_rel_def:
  same_frame_rel s s' ⇔
    s.contexts ≠ [] ∧
    LENGTH s'.contexts = LENGTH s.contexts ∧
    TL s'.contexts = TL s.contexts ∧
    SND (HD s'.contexts) = SND (HD s.contexts) ∧
    (FST (HD s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams ∧
    s'.txParams = s.txParams ∧
    s'.rollback.toDelete = s.rollback.toDelete ∧
    (let callee = (FST (HD s.contexts)).msgParams.callee in
       (∀a. a ≠ callee ⇒
            lookup_account a s'.rollback.accounts =
            lookup_account a s.rollback.accounts) ∧
       (∀a. a ≠ callee ⇒
            s'.rollback.tStorage a = s.rollback.tStorage a) ∧
       (lookup_account callee s'.rollback.accounts).balance =
         (lookup_account callee s.rollback.accounts).balance ∧
       (lookup_account callee s'.rollback.accounts).code =
         (lookup_account callee s.rollback.accounts).code ∧
       (lookup_account callee s.rollback.accounts).nonce ≤
         (lookup_account callee s'.rollback.accounts).nonce) ∧
    fSUBSET s.rollback.accesses.addresses
            s'.rollback.accesses.addresses ∧
    fSUBSET s.rollback.accesses.storageKeys
            s'.rollback.accesses.storageKeys ∧
    domain_compatible s.msdomain s'.msdomain ∧
    IS_PREFIX (FST (HD s'.contexts)).logs (FST (HD s.contexts)).logs ∧
    (FST (HD s.contexts)).gasUsed ≤ (FST (HD s'.contexts)).gasUsed ∧
    (FST (HD s.contexts)).addRefund ≤ (FST (HD s'.contexts)).addRefund ∧
    (FST (HD s.contexts)).subRefund ≤ (FST (HD s'.contexts)).subRefund
End
```

Quantities that are **deliberately free** in this relation, because they
do change during a frame:

- The head context's `stack`, `memory`, `pc`, `jumpDest`, `returnData`.
- The callee account's `storage` and `nonce`.
- The callee slot's transient storage.

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
- **Stop / Return / Revert / Invalid / OOG / non-outermost handled error /
  SELFDESTRUCT**: pop frame via `handle_step` → length changes → out of
  scope.
- **Outermost-frame error** (`handle_exception` with `n ≤ 1`, reraises):
  length unchanged. Effect: head `gasUsed` may rise (by `gasLeft`), head
  `returnData` may be cleared. Both free in `same_frame_rel`. ✓
- **`vfm_abort` error**: `handle_step` reraises immediately; state
  unchanged. Reflexivity of `same_frame_rel`. ✓

### SELFDESTRUCT

SELFDESTRUCT always pops its frame via `finish` → `handle_step` →
`handle_exception`, so every execution of SELFDESTRUCT changes
`LENGTH contexts`. It is therefore **automatically excluded** from
`same_frame_rel` by the length hypothesis of `step_same_frame`, without
any special-casing.

Its effects (value transfer to beneficiary, optional zeroing of sender
balance, appending to `toDelete`) are entirely confined to the pop
boundary, where they are handled by the `step_pops` lemma in
`vfmRunCallScript` and, for storage-preservation purposes, absorbed by the
fact that SELFDESTRUCT calls `access_address` on the beneficiary before
transferring — so the beneficiary is in `accesses.addresses`, and the
final-accesses-based theorem statement remains valid.

## Key derived theorems

### Within-frame (in `vfmCallFrameScript`)

```
Theorem run_within_frame_preserves:
  LENGTH es.contexts = d ∧ es.contexts ≠ [] ∧
  run_within_frame d es = SOME (r, es') ⇒
  same_frame_rel es es'
```

Named exported corollaries:

- `run_within_frame_preserves_txParams`
- `run_within_frame_preserves_toDelete`
- `run_within_frame_preserves_storage_outside_callee`
- `run_within_frame_preserves_tStorage_outside_callee`
- `run_within_frame_preserves_nonhead_contexts`
- `run_within_frame_preserves_head_msgParams`
- `run_within_frame_preserves_saved_rollback`
- `run_within_frame_preserves_callee_balance_and_code`
- `run_within_frame_callee_nonce_monotone`
- `run_within_frame_logs_grow`
- `run_within_frame_accesses_grow`
- `run_within_frame_gas_monotone`
- `run_within_frame_refund_monotone`
- `run_within_frame_domain_compatible`

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
  the gas-termination recipe — reused directly for `run_call_tr`.
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
- **SELFDESTRUCT within `same_frame_rel`.** Deliberately not handled —
  it is structurally excluded by the length hypothesis. The pop-boundary
  lemma captures its effects.
- **`code` mutation semantics.** Code can be installed at a newly-created
  contract's address via `handle_create`; elsewhere code is immutable. A
  tighter `run_call_preserves_code_outside_newly_created` theorem is a
  candidate follow-up.

## Ordered work plan

1. Add `run_call_def` to `vfmExecutionScript.sml`, rebuild `spec/`.
2. Create `spec/prop/vfmCallFrameScript.sml`:
   a. Define `same_frame_rel`, prove reflexivity and transitivity.
   b. Prove `cp m ⇒ same_frame_rel` bridge.
   c. Prove primitive-level `same_frame_rel` lemmas for non-`cp` writers
      (`write_storage`, `write_transient_storage`, `push_logs`,
      `update_gas_refund`, `access_slot`, `access_address`,
      `ensure_storage_in_domain`, `consume_gas`, `unuse_gas`,
      `increment_nonce-on-callee`).
   d. Prove `step_same_frame` by case analysis over `step_inst`, and
      handle the outermost-reraise path.
   e. Define `run_within_frame` and prove `run_within_frame_preserves`.
   f. Export named corollaries.
3. Create `spec/prop/vfmRunCallScript.sml`:
   a. Define `run_call_tr`, prove termination, prove `run_call_eq_tr`.
   b. Prove `step_pushes` and `step_pops` cross-boundary lemmas.
   c. Prove the across-call theorems by induction on `run_call_tr`.
   d. Export the headline theorem and companions.
4. Update `spec/prop/Holmakefile` if needed (currently `INCLUDES=..`, so
   probably no change).

## Open items to confirm before coding

- Predicate used for fset monotonicity in `same_frame_rel` — pick one
  (`fSUBSET`? `subdomain` analogue?) and be consistent.
- The exact shape of `step_pops` needed to discharge the cross-boundary
  case at `run_call_tr` induction — may simplify on inspection.
- Whether the `run_call_tr` equation requires a side condition
  `s.contexts ≠ []` (likely yes, as `run_tr` implicitly does via
  wellformedness).
