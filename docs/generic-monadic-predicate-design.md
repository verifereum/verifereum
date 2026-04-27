# Design: Generic Monadic Predicate Framework

## Problem

The `spec/prop/` directory contains 7+ independent monadic predicate
frameworks, each with their own composition lemmas and ~50–140
per-primitive/per-opcode leaf instances. The total is ~600 leaf lemmas
across ~26K lines. Almost all of this is redundant: the composition
structure is identical, and many predicates are entailed by stronger
ones.

## Goal

Replace this with a small generic framework that:

1. Proves composition lemmas once for a parameterised predicate
2. Provides implication bridges so stronger predicates derive weaker
   ones for free
3. Reduces the per-primitive leaf lemma count dramatically
4. Accommodates the "unusual" predicates (`decreases_gas`,
   `ignores_extra_domain`, `computes_minimal_domain`) that don't fit
   the simple `R s s'` pattern, without distorting the core design

## Classification of Existing Predicates

### Tier 1: Simple state-relation predicates

These have the form "if `m s = (r, s')` and a precondition on `s`,
then `R s s'`". All have identical composition structures.

| Predicate | Precondition on `s` | State relation `R s s'` |
|---|---|---|
| `preserves_rollback m` | (none) | `s'.rollback = s.rollback` |
| `preserves_storage m` | (none) | `∀a k. lookup_storage ... = ...` |
| `access_monotone m` | (none) | `toSet s.rb.accesses.SK ⊆ toSet s'.rb.accesses.SK` |
| `pns m` | (none) | `∀a k. ¬fIN (SK a k) s'.rb.accesses.SK ⇒ storage = storage` |
| `preserves_same_frame m` | `s.contexts ≠ []` | `same_frame_rel s s'` |
| `cp m` | `s.contexts ≠ []` | `cp_rel s s'` |
| `preserves_jumpDest m` | `s.contexts ≠ []` | `s'.contexts ≠ [] ∧ HD jumpDest = HD jumpDest` |
| `preserves_all_jumpDest_NONE m` | `all_jumpDest_NONE s` | `all_jumpDest_NONE s'` |

### Tier 2: State-indexed (precondition-parameterised) predicates

These generalise Tier 1 by parameterising over a precondition `p`:

| Predicate | Precondition `p s` | State relation |
|---|---|---|
| `psf p m` | `p s ∧ s.contexts ≠ []` | `same_frame_rel s s'` |
| `preserves_txParams` | (none) | `(SND (m s)).txParams = s.txParams` |
| `ignores_extra_domain_pred p m` | `p s ∧ s.msdomain = Enforce d1` | multi-clause (see below) |

### Tier 3: Non-standard predicates

These don't fit the `R s s'` pattern at all:

| Predicate | Why non-standard |
|---|---|
| `decreases_gas strict m` | Depends on `r` (the result), not just `s, s'`; strictness depends on INL/INR |
| `ignores_extra_domain_pred p m` | Quantifies over modified input states, not just `s, s'` |
| `computes_minimal_domain m` | Quantifies over modified input states and modes |
| `static_inv` | A concrete state invariant, not a monadic property |

## Design

### Core: `preserves` — a parameterised monadic property

```
Definition preserves_def:
  preserves (R: execution_state -> execution_state -> bool)
            (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ⇒ R s s'
End
```

This works for Tier 1 predicates with no precondition. For
predicates requiring `s.contexts ≠ []`, we fold it into the relation:

```
preserves (λs s'. s.contexts ≠ [] ⇒ R s s') m
```

Or equivalently, define a variant:

```
Definition preserves_when_def:
  preserves_when (pre: execution_state -> bool)
                (R: execution_state -> execution_state -> bool)
                (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ∧ pre s ⇒ R s s'
End
```

### Generic composition lemmas

Proved once for `preserves` / `preserves_when`:

```
Theorem preserves_bind[simp]:
  preserves R g ∧ (∀x. preserves R (f x)) ∧
  (∀s s' x. R s s' ∧ g s = (INL x, s') ⇒ R s' s'') ⇒   (* transitivity-like *)
  preserves R (bind g f)

Theorem preserves_ignore_bind[simp]:
  preserves R g ∧ preserves R f ⇒
  preserves R (ignore_bind g f)

Theorem preserves_handle:
  preserves R f ∧ (∀e. preserves R (h e)) ∧
  (* handle composition condition *) ⇒
  preserves R (handle f h)

Theorem preserves_cond[simp]:
  preserves R m1 ∧ preserves R m2 ⇒ preserves R (if b then m1 else m2)

Theorem preserves_case_option[simp]:
  preserves R m_none ∧ (∀x. preserves R (m_some x)) ⇒
  preserves R (case opt of NONE => m_none | SOME x => m_some x)

Theorem preserves_case_sum[simp]:
  (∀x. preserves R (f x)) ∧ (∀y. preserves R (g y)) ⇒
  preserves R (case s of INL x => f x | INR y => g y)

Theorem preserves_case_pair[simp]:
  (∀x y. preserves R (f x y)) ⇒ preserves R (case p of (x,y) => f x y)

Theorem preserves_let[simp]:
  (∀x. preserves R (f x)) ⇒ preserves R (let x = v in f x)

Theorem preserves_uncurry[simp]:
  (∀x y. preserves R (f x y)) ⇒ preserves R (UNCURRY f p)
```

Similarly for `preserves_when`:

```
Theorem preserves_when_bind[simp]:
  preserves_when pre R g ∧ (∀x. preserves_when pre R (f x)) ∧
  (∀s x s'. g s = (INL x, s') ∧ pre s ⇒ R s s') ∧
  (* R s s' ∧ pre s ⇒ pre s' — precondition forward closure *)
  preserves_when pre R (bind g f)
```

### Instantiations — Tier 1

Each existing predicate becomes a one-line instantiation:

```
Theorem preserves_rollback_alt:
  preserves_rollback m ⇔ preserves (λs s'. s'.rollback = s.rollback) m
Proof ... QED

(* Leaf lemmas derived via: *)
Theorem return_preserves_rollback[simp]:
  preserves_rollback (return x)
Proof
  irule (GEN_ALL preserves_return) >> simp[preserves_rollback_alt]
QED
```

Or more elegantly, just register the relation and let the simp set
do the rest:

```
Overload rollback_rel = ``λs s'. s'.rollback = s.rollback``

Theorem preserves_rollback_eq:
  preserves_rollback m ⇔ preserves rollback_rel m
```

Then the generic `[simp]` composition lemmas for `preserves` give all
the bind/ignore_bind/handle/cond/case lemmas for free.

### Instantiations — Tier 2 (psf)

The `psf p m` predicate is `preserves_when p same_frame_rel m`,
extended with the `s.contexts ≠ []` guard. We can either:

(a) Fold the guard into the relation:
```
psf_rel ≡ λs s'. s.contexts ≠ [] ∧ same_frame_rel s s'
```
Then `psf p m = preserves_when p psf_rel m`.

(b) Fold the guard into the precondition:
```
psf p m = preserves_when (λs. p s ∧ s.contexts ≠ []) same_frame_rel m
```

Option (b) is cleaner because it keeps `same_frame_rel` pure and
lets us reuse the `preserves_when` composition lemmas directly.

The specialised getter-bind rules (`psf_bind_get_callee`, etc.) are
specific to the `same_frame_rel` structure and would remain in
`vfmSameFrame`. These are not part of the generic framework.

### Tier 3 — What stays outside

The following predicates cannot be expressed as `preserves R` because
they quantify over modified input states (not just `s, s'`):

- **`decreases_gas`**: depends on whether the result is INL or INR
  (strict mode), and relates gas usage across `s, s'` via a complex
  context-level condition.
- **`ignores_extra_domain_pred`**: quantifies over `s with msdomain
  := Enforce d2` and `s'` such that `domain_compatible s s'`.
- **`computes_minimal_domain`**: quantifies over Collect/Enforce mode
  changes.

These stay as specialised frameworks. However, their composition
lemmas still follow similar patterns, so we can provide a
**second generic framework** for "result-indexed" predicates:

```
Definition preserves_result_def:
  preserves_result (P : α execution_result -> execution_state -> execution_state -> bool)
                   (m : α execution) ⇔
    ∀s r s'. m s = (r, s') ⇒ P r s s'
End
```

`decreases_gas` can then be expressed as:

```
decreases_gas_rel strict ≡
  λr s s'.
    case s.contexts of
    | [] => s'.contexts = []
    | (c,r')::crs =>
      ∃c''. s'.contexts = (c'',r')::crs ∧
              c''.msgParams.gasLimit = c.msgParams.gasLimit ∧
              ... ∧
              if strict ∧ ISL r then c.gasUsed < c''.gasUsed
              else c.gasUsed ≤ c''.gasUsed
```

The composition lemmas for `preserves_result` account for the fact
that `r` is threaded through `bind`:

```
Theorem preserves_result_bind:
  preserves_result P g ∧
  (∀x. preserves_result (P_cont x) (f x)) ∧
  (∀s r s' x. g s = (INL x, s') ∧ P (INL x) s s' ⇒ P_cont x (INL x) s s') ∧
  (∀x r'' s''. f x s' = (r'', s'') ∧ P_cont x r'' s' s'' ⇒ P r'' s s'')
  ⇒ preserves_result P (bind g f)
```

For `ignores_extra_domain_pred`, the shape is different enough that
it should remain standalone, but many of its leaf lemmas can be
derived from `computes_minimal_domain` lemmas via a bridge (item 3 in
the refactoring review).

### Implication Bridges

Once all Tier 1 predicates are `preserves R` instances, implication
bridges become trivial:

```
Theorem preserves_mono:
  (∀s s'. R1 s s' ⇒ R2 s s') ⇒
  preserves R1 m ⇒ preserves R2 m
```

Then proving `preserves_same_frame ⇒ cp` reduces to proving
`same_frame_rel ⇒ cp_rel`:

```
Theorem same_frame_rel_imp_cp_rel:
  same_frame_rel s s' ⇒ cp_rel s s'
Proof
  rw[same_frame_rel_def, cp_rel_def, callee_local_changes_def] >> ...
QED
```

The full hierarchy:

```
same_frame_rel
  ⇒ rollback_rel        (λs s'. s'.rollback = s.rollback)   [actually weaker: callee_local_changes]
  ⇒ cp_rel              (head msgParams + rollback.accounts/tStorage/toDelete)
  ⇒ storage_rel         (storage at every a,k unchanged)
  ⇒ pns_rel             (storage at non-accessed a,k unchanged)
  ⇒ access_monotone_rel (storageKeys monotone)

same_frame_rel ⇒ access_monotone_rel
rollback_rel ⇒ storage_rel ⇒ pns_rel
rollback_rel ∧ access_monotone_rel ⇒ pns_rel  [stronger composition rule]
```

Wait — `same_frame_rel` does **not** imply `rollback_rel`, because
`callee_local_changes` allows the callee's nonce/storage/code to
change and arbitrary balance transfers. So the hierarchy splits:

```
same_frame_rel
  ⇒ cp_rel
  ⇒ access_monotone_rel (addresses + storageKeys monotone)

rollback_rel
  ⇒ storage_rel
  ⇒ pns_rel

same_frame_rel ⊓ rollback_rel
  ⇒ storage_rel at non-callee addresses  [from callee_local_changes]
  ⇒ pns_rel at non-callee + access-monotone at callee
```

The key insight: `same_frame_rel` + `access_monotone_rel` ≠ `pns_rel`
directly. We need `callee_local_changes` (from `same_frame_rel`) plus
`access_monotone` to get `pns` at the callee address. This is exactly
what `step_inst_preserves_non_accessed_storage` does case-by-case.

### Leaf Lemmas — Primitive Effect Characterisation

Instead of proving each primitive preserves each predicate
separately, define a small set of **primitive effect lemmas** that
characterise what each primitive does:

```
Theorem get_current_context_effect:
  get_current_context s = (INL (FST (HD s.contexts)), s)      (if s.contexts ≠ [])
  get_current_context s = (INR (SOME StackUnderflow), s)     (if s.contexts = [])
```

From these, all preservation lemmas follow mechanistically via
`preserves_mono` + `preserves_return` etc. For example:

```
(* get_current_context preserves rollback: trivial from state unchanged *)
Theorem preserves_rollback_get_current_context[simp]:
  preserves_rollback get_current_context
Proof
  irule (GEN_ALL preserves_return) >> simp[return_def, get_current_context_def]
QED
```

But with the generic framework:

```
Theorem rollback_rel_get_current_context:
  rollback_rel s (SND (get_current_context s))
Proof simp[get_current_context_def, return_def, fail_def] QED

(* Then: *)
Theorem preserves_rollback_get_current_context[simp]:
  preserves_rollback get_current_context
Proof irule preserves_rel_def >> metis_tac[rollback_rel_get_current_context] QED
```

For "writer" primitives like `set_current_context`, we need a
parameterised effect lemma:

```
Theorem set_current_context_effect:
  set_current_context c s = (INL (), s with contexts := UPDATE_HEAD ... s.contexts)
    — UPDATE_HEAD only modifies FST; SND is unchanged; FST.msgParams unchanged
```

Then preservation of `rollback_rel`, `cp_rel`, etc. follows from the
structure of the update.

### Precompile Family

With the generic framework, prove one dispatch theorem per predicate:

```
Theorem preserves_rollback_dispatch_precompiles[simp]:
  preserves_rollback (dispatch_precompiles a)
Proof
  rw[dispatch_precompiles_def] >> rpt IF_CASES_TAC >> rw[]
QED
```

This folds 18 separate lemmas into 1. The individual precompile
lemmas are kept only if needed as `[simp]` entry points for the
dispatch case-split.

## Migration Strategy

The migration should be done in stages to avoid breaking the build:

### Stage 0: Create the new theory `vfmPreserves`

Put it in `spec/prop/vfmPreservesScript.sml` with no ancestor changes.
It depends only on `vfmExecution` (for the monad types). Contains:

- `preserves_def`, `preserves_when_def`
- Generic composition lemmas (bind, ignore_bind, handle, cond, case)
- `preserves_mono`, `preserves_when_mono` (implication bridges)
- `preserves_when_imp_preserves` (weakening the precondition)

### Stage 1: Add `preserves`-based alternative definitions

In each existing theory, add an alternative definition:

```
Theorem preserves_rollback_alt:
  preserves_rollback m ⇔ preserves rollback_rel m
```

This doesn't change any existing code but establishes the link.

### Stage 2: Add implication bridges between predicates

In `vfmStoragePredicates`, prove `rollback_rel ⇒ storage_rel ⇒ pns_rel`.
In `vfmSameFrame`, prove `same_frame_rel ⇒ cp_rel` and
`same_frame_rel ⇒ access_monotone_rel`.

### Stage 3: Derive leaf lemmas via bridges

Replace proofs like:

```
Theorem cp_get_current_context[simp]: cp get_current_context
Proof rw[cp_def, ...] QED
```

with:

```
Theorem cp_get_current_context[simp]: cp get_current_context
Proof irule preserves_same_frame_imp_cp >> simp[] QED
```

Do this incrementally, one theory at a time, verifying each builds.

### Stage 4: Remove redundant leaf lemmas

Once all downstream consumers use the bridge-derived versions, remove
the standalone proofs. This can be done lazily — old lemmas that are
no longer `[simp]` entry points can simply be left as dead code initially.

### Stage 5 (optional): Refactor Tier 3 predicates

Factor `decreases_gas` into `preserves_result`-based form. Prove
`computes_minimal_domain ⇒ ignores_extra_domain` bridge.

## Design Decisions to Confirm

### Q1: Should `preserves` include the `s.contexts ≠ []` guard?

**Option A**: Include it in the relation:
```
preserves (λs s'. s.contexts ≠ [] ⇒ R s s') m
```

**Option B**: Keep `preserves` guard-free, use `preserves_when` for
guarded variants.

**Recommendation**: Option B. This keeps the generic framework simple
and lets `preserves_when pre R` subsume all cases. The unguarded
`preserves` is the natural "strongest" statement.

### Q2: Should primitive effect lemmas live in a separate theory?

**Option A**: One theory `vfmPrimitiveEffects` with all primitive
characterisations.

**Option B**: Each theory keeps its own primitive lemmas but derives
them from the effect characterisation.

**Recommendation**: Option B for now (less disruption). The effect
lemmas can be introduced locally as alternative proof methods without
moving definitions between theories.

### Q3: Multi-property composition (`pns` pattern)

`pns` requires TWO properties to compose: `pns_rel` (storage not
changed at non-accessed slots) AND `access_monotone_rel` (access list
grows). Neither alone composes for `pns`; you need both.

This is naturally handled in the generic framework by observing
that `pns m` holds iff `preserves pns_rel m ∧ preserves access_monotone_rel m`.

A generic conjunction rule makes this work:

```
Theorem preserves_conj:
  preserves R1 m ∧ preserves R2 m ⇒ preserves (λs s'. R1 s s' ∧ R2 s s') m
```

And each component composes independently via `preserves_bind` since
each individual `Ri` is transitive (set subset, equality, etc.).

This pattern generalises: any multi-property predicate (like `pns`)
splits into independent `preserves R_i` components that compose
separately.

### Q4: How to handle `bind` for `preserves R` when `R` is not transitive?

The generic `preserves_bind` requires some form of transitivity or
residual closure. For `preserves (λs s'. s'.rollback = s.rollback)`:
the relation IS transitive (it's equality). For `same_frame_rel`: it
IS transitive. For `access_monotone`: the set-subset relation is
transitive.

But for non-transitive relations, we would need:

```
preserves R g ∧ (∀x. preserves R (f x)) ∧
(∀s s' x. g s = (INL x, s') ∧ R s s' ⇒ R s s'' ∧ R s' s'')  (?)
```

Actually, since `R s' s''` comes from `f x s' = (_, s'')` and
`preserves R (f x)`, we get `R s' s''`. And we have `R s s'` from
`g`. To conclude `R s s''`, we need `R s s' ∧ R s' s'' ⇒ R s s''`,
i.e., transitivity.

**Decision**: Require `R` to be transitive (or add it as a
side-condition on bind). All existing relations happen to be
transitive, so this is fine. We can make `preserves_bind` take an
optional transitivity argument, or just prove it for each specific R
as needed.

Actually, a cleaner approach: make `preserves_bind` require the
following condition:

```
∀s s' s''. R s s' ∧ R s' s'' ⇒ R s s''
```

as a parameter or side-goal. For all existing relations this is
trivially provable, and it makes the theorem maximally general.

### Q5: Should the generic framework live in `vfmExecutionProp`?

It depends only on the monad types. It could go into `vfmExecutionProp`
(where `bind_def`, `return_def` etc. already live), or into a new
standalone theory.

**Recommendation**: New theory `vfmPreserves` in `spec/prop/`.
It's a "library" theory that doesn't depend on any other prop
theories. This keeps the dependency graph clean and avoids polluting
`vfmExecutionProp` with abstract predicate machinery.

## File Layout

```
spec/prop/vfmPreservesScript.sml    (NEW — generic framework)
spec/prop/vfmSameFrameScript.sml    (modified — use preserves_when + bridges)
spec/prop/vfmStoragePredicatesScript.sml  (modified — use preserves + bridges)
spec/prop/vfmStaticCallsScript.sml  (modified — derive cp from preserves_same_frame)
spec/prop/vfmJumpDestScript.sml     (modified — use preserves/preserves_when)
...
```

## Estimated Impact

| Item | Current leaf lemmas | After refactoring |
|---|---|---|
| Composition lemmas | ~50 (7 frameworks × 7 combinators) | ~14 (2 variants × 7) |
| Implication bridges | 0 | ~5 |
| `cp` leaf lemmas | ~41 | 0 (derived from `preserves_same_frame`) |
| `preserves_rollback` leaf lemmas | ~257 | ~50 (most derived from `preserves`) |
| `preserves_storage` leaf lemmas | ~20 | ~5 (derived from `preserves_rollback`) |
| `access_monotone` leaf lemmas | ~10 | 0 (derived from `preserves_same_frame`) |
| Precompile leaf lemmas | ~102 (6 frameworks × 17) | ~6 (1 per framework) |
| `preserves_txParams` leaf lemmas | ~125 | ~20 (most derived from `preserves`) |
| **Total** | **~600+** | **~100** |

Net code reduction: estimated **10–15K lines** saved out of 26K.
