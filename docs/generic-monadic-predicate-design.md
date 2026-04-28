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

## Current Status

Stages 0–4 are **complete and building**. Stages 5–7 are not started.

| Stage | Description | Status |
|---|---|---|
| 0 | Create `vfmPreserves` theory | ✅ Done |
| 1 | State-relation definitions + equivalences | ✅ Done |
| 2 | Reflexivity/transitivity + implication bridges | ✅ Done |
| 3 | Derive composition rules from generic framework | ✅ Done |
| 4 | Extend framework to vfmTxParams + vfmJumpDest | ✅ Done |
| 5 | Consolidate per-opcode leaf lemmas | Not started |
| 6 | Remove redundant leaf lemmas | Not started |
| 7 | Refactor Tier 3 predicates (optional) | Not started |

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
| `preserves_txParams` | (none) | `txParams_rel s s'` (now converted) |
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

Then proving that one `preserves` instance implies another reduces
to proving the implication between the underlying state relations:

```
Theorem preserves_mono:
  (∀s s'. R1 s s' ⇒ R2 s s') ⇒
  preserves R1 m ⇒ preserves R2 m
```

**However**, `same_frame_rel` does **not** imply `cp_rel` or
`rollback_rel`. The `callee_local_changes` component of
`same_frame_rel` allows the callee's storage, code, and nonce to
change and permits arbitrary balance transfers, while `cp_rel`
requires full rollback equality. So the hierarchy is not a simple
chain; it splits into three strands:

```
rollback_rel
  ⇒ storage_rel
  ⇒ pns_rel

rollback_rel ⇒ access_monotone_sk_rel   (vacuously: unchanged = ⊆)

same_frame_rel
  ⇒ access_monotone_sk_rel           (from ⊆ constraints in definition)
  ⇒ access_monotone_addr_rel
  ⇒ non_callee_storage_rel callee     (from callee_local_changes)
  ⇒ txParams_rel                     (s'.txParams = s.txParams)
  ⇒ msdomain_compatible_rel         (msdomain_compatible s.ms s'.ms)

cp_rel
  ⇒ storage_rel                     (accounts preserved ⇒ storage at every a,k preserved)
  ⇒ pns_rel                        (via storage_rel)

NOTE: cp_rel does NOT imply rollback_rel or access_monotone_sk_rel.
cp preserves rollback.accounts/tStorage/toDelete but says nothing
about rollback.accesses — operations like access_address, access_slot
modify accesses while being cp. cp and access_monotone are orthogonal
properties.
```

Note: `cp_rel ⇒ same_frame_rel` does **not** hold either. `cp_rel`
says nothing about callee-local vs non-callee changes to
storage/code/nonce, about access-list monotonicity, or about
msdomain compatibility. The two relations overlap but neither
subsumes the other.

The key insight for `pns`: `same_frame_rel` alone is **not**
sufficient to derive `pns_rel`. We need `callee_local_changes` +
`access_monotone` to get `pns` at the callee address. This is
exactly what `step_inst_preserves_non_accessed_storage` does
case-by-case, and what the `pns_bind_access_monotone` composition
rule captures structurally.

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

The migration is done in stages to avoid breaking the build:

### Stage 0: Create the new theory `vfmPreserves` ✅ DONE

`spec/prop/vfmPreservesScript.sml` (385 lines).
Depends only on `vfmExecution` (for the monad types). Contains:

- `preserves_def`, `preserves_when_def`
- Generic composition lemmas: `preserves_bind/ignore_bind/handle/cond/case_option/case_sum/case_pair/let/uncurry`
- Generic composition lemmas: `preserves_when_bind/ignore_bind/handle/cond/case_option/case_sum/case_pair/let/uncurry`
- Generalised variants: `preserves_when_bind_gen`, `preserves_when_ignore_bind_gen`, `preserves_when_handle_gen`
- Primitive lemmas: `preserves_return/fail/reraise/assert`, `preserves_when_return/fail/reraise/assert`
- Implication bridges: `preserves_mono`, `preserves_when_mono_R`, `preserves_when_mono_pre`
- Conjunction: `preserves_conj/elim1/elim2`, `preserves_when_conj/elim1/elim2`
- Weakening: `preserves_imp_preserves_when`, `preserves_when_T_imp_preserves`, `preserves_eq_preserves_when_T`

### Stage 1: Add `preserves`-based alternative definitions ✅ DONE

Each existing predicate theory now has a state-relation definition and
equivalence theorem:

| Theory | State relation | Equivalence theorem |
|---|---|---|
| vfmStoragePredicates | `rollback_rel`, `storage_rel`, `access_monotone_sk_rel`, `access_monotone_addr_rel`, `pns_rel` | `preserves_rollback_eq_preserves`, `preserves_storage_eq_preserves`, `access_monotone_eq_preserves`, `pns_eq_preserves` |
| vfmSameFrame | `same_frame_rel` (pre-existing) | `preserves_same_frame_eq_preserves_when` |
| vfmStaticCalls | `cp_rel` | `cp_eq_preserves_when` |
| vfmTxParams | `txParams_rel` | `preserves_txParams_eq_preserves` |
| vfmJumpDest | `jumpDest_rel` | `preserves_jumpDest_eq_preserves_when` |

### Stage 2: Add implication bridges between predicates ✅ DONE

**Valid bridges proved:**
- `rollback_rel ⇒ storage_rel ⇒ pns_rel`
- `rollback_rel ⇒ access_monotone_sk_rel`, `rollback_rel ⇒ access_monotone_addr_rel`
- `same_frame_rel ⇒ access_monotone_sk_rel`, `same_frame_rel ⇒ access_monotone_addr_rel`
- `same_frame_rel ⇒ non_callee_storage_rel`, `same_frame_rel ⇒ txParams_rel`, `same_frame_rel ⇒ msdomain_compatible`
- `cp_rel ⇒ storage_rel`, `cp_rel ⇒ pns_rel`

**Bridges that do NOT hold (correctly absent):**
- `same_frame_rel ⇒ cp_rel` (callee_local_changes allows storage/balance changes)
- `cp_rel ⇒ same_frame_rel` (cp says nothing about callee-local changes or access monotonicity)
- `cp_rel ⇒ rollback_rel` (cp doesn't preserve `rollback.accesses`)
- `cp_rel ⇒ access_monotone_sk_rel` (cp and access_monotone are orthogonal)

### Stage 3: Derive per-predicate composition rules from generic framework ✅ DONE

**vfmStoragePredicates (unguarded `preserves R` pattern):**

Reflexivity and transitivity lemmas proved for `rollback_rel`,
`storage_rel`, `access_monotone_sk_rel`, `access_monotone_addr_rel`.
`pns_rel` has refl but NOT trans (correctly — it is not transitive).

Composition rules derived:
- `preserves_rollback_*`: 12 rules (bind, ignore_bind, return, fail, reraise, cond, assert, case_pair, case_sum, case_option, let, uncurry)
- `preserves_storage_*`: 9 rules
- `access_monotone_*`: 3 rules (bind, ignore_bind, cond)
- `pns`: 4 from generic (return, fail, reraise, cond) + 4 specialised (bind_access_monotone, bind_preserves_storage, handle, ignore_bind_access_monotone)
- Predicate-level bridges via `preserves_mono`: `preserves_rollback_imp_preserves_storage`, `access_monotone_of_preserves_rollback`, `preserves_rollback_imp_pns`, etc.

**vfmSameFrame (guarded `preserves_when pre R` pattern):**

`same_frame_rel_refl`, `same_frame_rel_trans`, `same_frame_rel_contexts_ne` proved.
12 composition rules derived from `preserves_when_*`.
`psf_*` composition rules NOT changed (getter-bind pattern, non-trivial `p`/`p_cont`).

**vfmStaticCalls (guarded `preserves_when pre R` pattern):**

`cp_rel_refl`, `cp_rel_trans`, `cp_rel_contexts_ne` proved.
8 composition rules derived from `preserves_when_*`.

**vfmStoragePredicates (cp_rel implication bridges):**

`cp_rel ⇒ storage_rel` proved directly (accounts preserved).
`cp_rel ⇒ pns_rel` proved via `storage_rel`.
`cp_rel ⇒ rollback_rel` and `cp_rel ⇒ access_monotone_sk_rel` correctly absent.

### Stage 4: Extend the framework to remaining theories ✅ DONE

**vfmTxParams** (`preserves_txParams`):
- `txParams_rel_def`: `txParams_rel s s' ⇔ s'.txParams = s.txParams`
- `preserves_txParams_def` (direct form) + `preserves_txParams_eq_preserves:`
  `preserves_txParams m ⇔ preserves txParams_rel m`
- `txParams_rel_refl[simp]`, `txParams_rel_trans`
- 5 composition rules derived: `preserves_txParams_bind/ignore_bind/handle/cond/domain_check`
- All ~125 leaf lemmas converted from raw `(SND (m s)).txParams = s.txParams`
  to predicate form `preserves_txParams m`
- 4 backward-compat raw-form theorems for downstream consumers:
  `step_preserves_txParams`, `handle_step_preserves_txParams`,
  `step_call_preserves_txParams`, `run_preserves_txParams`
- `return/fail/reraise/assert` derived from generic `preserves_return/fail/reraise/assert`

**vfmJumpDest** (`preserves_jumpDest`):
- `jumpDest_rel_def`: guarded relation `s'.contexts ≠ [] ∧ (s.contexts ≠ [] ⇒ HD jumpDest equality)`
- `preserves_jumpDest_eq_preserves_when:`
  `preserves_jumpDest m ⇔ preserves_when (λs. s.contexts ≠ []) jumpDest_rel m`
- `jumpDest_rel_refl`, `jumpDest_rel_trans`, `jumpDest_rel_contexts_ne`
- 12 composition rules derived (bind/ignore_bind/handle/cond + case_*/let/uncurry)
- `return/fail/reraise/assert` derived from generic `preserves_when_return/fail/reraise/assert`

**vfmJumpDest** (`preserves_all_jumpDest_NONE`) — NOT CONVERTED:
- The precondition `all_jumpDest_NONE s` does not fit cleanly into `preserves_when`
  because the state relation `λs s'. all_jumpDest_NONE s'` is degenerate
  (ignores the input state) and reflexivity doesn't hold unconditionally.
- Left as-is with hand-proved composition rules.
- Could be addressed in a future pass using the relation
  `λs s'. all_jumpDest_NONE s ⇒ all_jumpDest_NONE s'` with `preserves`
  (reflexivity and transitivity are trivially satisfied).
- Decision to defer: the benefit is small (only 3 composition rules).

### Stage 5: Consolidate per-opcode leaf lemmas — NOT STARTED

This is where the major line-count reductions come from. The current
codebase has ~18 per-precompile leaf lemmas per predicate (~100 total)
and ~100+ per-opcode `preserves_same_frame` leaf lemmas.

**Precompile dispatch consolidation:**
Instead of proving 18 separate `preserves_rollback_precompile_*` lemmas,
prove one dispatch theorem:
```
Theorem preserves_rollback_dispatch_precompiles[simp]:
  preserves_rollback (dispatch_precompiles a)
```
This already exists; the individual lemmas can be de-registered from
`[simp]` if the dispatch theorem fires instead.

**Opcode dispatch consolidation (vfmSameFrame):**
The ~100 `preserves_same_frame_step_inst_*` lemmas are currently
proved one-by-one. Many share structure (stack ops, arithmetic ops,
comparison ops). Grouping them into families with shared tactics
or deriving them from `cp_step_inst_non_call` via bridges would
reduce the proof code significantly.

Note: `same_frame_rel ⇒ cp_rel` does **not** hold (the relations are
orthogonal), so direct bridge derivation is not possible here. The
reduction must come from better tactic hygiene, not from bridges.

### Stage 6: Remove redundant leaf lemmas — NOT STARTED

Once Stage 5 has provided replacement `[simp]` entry points
(dispatch theorems, family tactics), the individual leaf lemmas
that are no longer `[simp]` can be removed. This can be done lazily
— old lemmas that are no longer `[simp]` entry points can simply be
left as dead code initially.

### Stage 7 (optional): Refactor Tier 3 predicates — NOT STARTED

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
spec/prop/vfmPreservesScript.sml    (385 lines — generic framework)
spec/prop/vfmStoragePredicatesScript.sml  (1727 lines — rollback/storage/pns/access_monotone + bridges)
spec/prop/vfmSameFrameScript.sml    (2471 lines — same_frame/psf + bridges)
spec/prop/vfmStaticCallsScript.sml  (1817 lines — cp + static_inv)
spec/prop/vfmTxParamsScript.sml     (944 lines — txParams, fully converted to preserves)
spec/prop/vfmJumpDestScript.sml    (2288 lines — jumpDest converted, all_jumpDest_NONE kept)
```

Dependency graph:
```
vfmPreserves → vfmExecution
vfmStaticCalls → vfmExecution, vfmPreserves
vfmSameFrame → vfmStaticCalls, vfmTxParams, vfmPreserves
vfmStoragePredicates → vfmStaticCalls, vfmSameFrame, vfmPreserves
vfmTxParams → vfmExecution, vfmPreserves
vfmJumpDest → vfmSameFrame, vfmPreserves
```

## Estimated Impact

### Already achieved (Stages 0–4)

| Item | Before | After Stages 0–4 |
|---|---|---|
| Composition rules | ~50 hand-proved (7 frameworks × 7 combinators) | ~14 generic + ~55 one-line derivations |
| Implication bridges | 0 | ~18 (relation-level + predicate-level) |
| New state-rel definitions | 0 | 9 (`*_rel_def`) |
| New refl/trans lemmas | 0 | ~16 |
| `cp` leaf lemmas | ~41 | ~41 (cp_rel ≠ same_frame_rel; no bridge reduction) |
| `preserves_txParams` leaf lemmas | ~125 raw-form | ~125 predicate-form + 4 backward-compat |
| `preserves_jumpDest` leaf lemmas | ~80 (hand-proved comp rules) | ~80 (3 comp rules now generic-derived, +9 new comp rules added) |
| `preserves_rollback` leaf lemmas | ~257 | ~257 (leaf proofs unchanged; composition rules genericised) |
| `preserves_storage` leaf lemmas | ~20 | ~20 |
| `access_monotone` leaf lemmas | ~10 | ~10 |
| `pns` leaf lemmas | ~4 | ~4 |
| `preserves_all_jumpDest_NONE` | ~70 | ~70 (not converted; degenerate relation) |

Stages 0–4 primarily deliver **structural benefits**:
- One place to add new combinators (add to `vfmPreserves`, all predicates inherit)
- Consistent proof patterns across all predicate theories
- Bridges between predicates (e.g., `preserves_rollback m ⇒ preserves_storage m`)
- A clear hierarchy of state relations with proven implications
- vfmTxParams fully in predicate form (enabling future `preserves_mono` bridges)

They do **not** significantly reduce line count — leaf lemmas are still
needed as `[simp]` entry points, and new definitions/theorems add ~100 lines.

### Projected (Stages 5–6)

| Item | After Stages 0–4 | After Stages 5–6 |
|---|---|---|
| Precompile leaf lemmas | ~102 (6 frameworks × 17) | ~6 (1 dispatch per framework) |
| `preserves_same_frame` leaf lemmas | ~100+ (per opcode) | ~20–30 (family tactics + consolidation) |
| Redundant `[simp]` leaf lemmas | various | 0 (removed in Stage 6) |
| **Line-count reduction** | | **~5–8K lines saved** |

Note: The original estimate of **10–15K lines saved** was based on
the assumption that `cp` leaf lemmas could be derived from
`preserves_same_frame` via a bridge. Since `same_frame_rel ⇒ cp_rel`
does not hold, that reduction is not available. The realistic
saving is ~5–8K lines, mostly from precompile dispatch and opcode
family consolidation.
