# Refactoring Review: `spec/prop/` Theories

Date: 2026-04-27

## Scope

All 15 HOL4 theory scripts in `spec/prop/`, totalling ~26K lines.
These theories establish monadic predicate frameworks for reasoning
about what effects EVM step/opcode computations have on the execution
state, and lift those through `run_within_frame`, `run_call`, and
`run`.

## 1. Central Problem: Massive Redundancy Across Monadic Predicate Hierarchies

The most significant factoring issue is that **7+ independent monadic
predicate frameworks** each define their own composition lemmas (bind,
ignore_bind, handle, cond, case) and then prove ~50–140
per-primitive/per-opcode leaf instances. The total comes to roughly
**600+ leaf lemmas** across the codebase, occupying most of the ~26K
lines. The frameworks are:

| Theory | Predicate | Leaf count |
|---|---|---|
| `vfmTxParams` | `preserves_txParams` | ~125 |
| `vfmMsdomainPreserved` | `SND_*_msdomain` | 18 |
| `vfmStoragePredicates` | `preserves_rollback`, `preserves_storage`, `access_monotone`, `pns` | ~138 |
| `vfmStaticCalls` | `cp` | ~125 |
| `vfmSameFrame` | `preserves_same_frame`, `psf` | ~254 |
| `vfmDecreasesGas` | `decreases_gas` | ~161 |
| `vfmDomainSeparation` | `ignores_extra_domain`, `ignores_extra_domain_pred` | ~276 |
| `vfmDomainCollection` | `computes_minimal_domain` | ~107 |
| `vfmJumpDest` | `preserves_jumpDest`, `preserves_all_jumpDest_NONE` | ~231 |

**Refactoring opportunity**: Define a single generic monadic predicate
framework parameterised by a state relation `R s s'`:

```
preserves (R: execution_state -> execution_state -> bool) m ⇔
  ∀s r s'. m s = (r, s') ∧ s.contexts ≠ [] ⇒ R s s'
```

with generic `[simp]` composition lemmas (`preserves_bind`,
`preserves_ignore_bind`, `preserves_handle`, `preserves_cond`, etc.).
Then each specific predicate becomes a one-line instantiation:

- `preserves_same_frame = preserves same_frame_rel`
- `preserves_rollback = preserves (λs s'. s'.rollback = s.rollback)`
- `preserves_storage = preserves (λs s'. ∀a k. lookup_storage ... = ...)`
- etc.

The per-primitive leaf lemmas could also be derived from a smaller set
of "primitive effect characterisation" lemmas that describe what each
primitive does to the state, rather than re-proving 7 different
preservation properties of each primitive independently.

## 2. Missing Implication Bridges Between Predicates

There are logical entailments between the predicates that are never
made formal, forcing parallel proof trails:

- **`preserves_same_frame ⇒ cp`**: `same_frame_rel` implies the head
  context's msgParams is unchanged and rollback.accounts/tStorage/toDelete
  are unchanged at non-callee addresses — strictly stronger than `cp`.
  Yet ~41 `cp_*` lemmas in `vfmStaticCalls` are proved independently of
  the ~79 `preserves_same_frame_step_inst_*` lemmas in `vfmSameFrame`.
  A single bridge theorem `preserves_same_frame_imp_cp` would let you
  derive all `cp` lemmas for free from the `preserves_same_frame`
  lemmas.

- **`preserves_same_frame ⇒ preserves_rollback`**: `same_frame_rel`
  includes `callee_local_changes`, which is weaker than full rollback
  preservation, but the comment in `vfmRunCall` even sketches this
  ("preserves_storage + preserves_same_frame ⇒
  preserves_pushed_rb_storage") without making it formal.

- **`preserves_same_frame ⇒ access_monotone`**: `same_frame_rel`
  includes `toSet s.rollback.accesses.addresses ⊆ ...` and
  `toSet s.rollback.accesses.storageKeys ⊆ ...`, which is exactly
  `access_monotone`.

- **`preserves_rollback ⇒ preserves_storage`**: This exists as
  `[simp]` in `vfmStoragePredicates`, but the reverse direction of
  `preserves_storage ⇒ pns` (`pns_of_preserves_storage`) exists
  while `preserves_rollback ⇒ pns`
  (`preserves_rollback_imp_pns`) is proved separately. The full
  hierarchy should be:
  ```
  preserves_same_frame ⇒ preserves_rollback ⇒ preserves_storage ⇒ pns
  preserves_same_frame ⇒ access_monotone
  preserves_rollback ∧ access_monotone ⇒ pns (stronger than preserves_storage alone)
  ```

Making these bridges explicit would eliminate roughly half the leaf
lemmas across the codebase.

## 3. `cp` and `preserves_same_frame` Should Be Related

`cp` (context-preserving, in `vfmStaticCalls`) and
`preserves_same_frame` (in `vfmSameFrame`) capture overlapping
concepts. Specifically:

- `cp` says: rollback.accounts/tStorage/toDelete unchanged + head
  context msgParams/logs unchanged + tail unchanged
- `preserves_same_frame` says: all of `cp` **plus**
  callee-local-changes (non-callee storage/code/nonce preserved,
  callee nonce monotone) + access list monotone + msdomain
  compatible + log prefix/refund monotone

Since `preserves_same_frame` is strictly stronger, every `cp` leaf
lemma is redundant. The fact that `vfmStaticCalls` (125 theorems)
and `vfmSameFrame` (254 theorems) exist as independent hierarchies
indicates the theories evolved before the relationship was
understood. A clean factoring would:

1. Make `cp` a derived notion: `cp m ⇔ preserves (λs s'. cp_rel s s') m`
   where `cp_rel` is the state relation capturing `cp`'s constraints
2. Prove `same_frame_rel ⇒ cp_rel`
3. Derive all `cp` lemmas from `preserves_same_frame` via this bridge

## 4. Weakness in `step_inst_preserves_non_accessed_storage`

The main opcode-level lemma in `vfmStoragePredicates`:

```
step_inst op s = (r, s') ∧ s.contexts ≠ [] ∧ ¬is_call op ⇒
  ∀a k. ¬fIN (SK a k) s'.rollback.accesses.storageKeys ⇒
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
```

The `¬is_call op` hypothesis is **too restrictive**. Call-family
opcodes that abort (e.g., `step_call` returning INL at same frame
length) also preserve non-accessed storage. This is proved separately
as `step_call_same_frame_preserves_storage` and
`step_create_same_frame_preserves_storage` in
`vfmStoragePredicates`, and then
`is_call_same_frame_preserves_storage` combines them. But
`step_inst_preserves_non_accessed_storage` doesn't subsume these. A
stronger theorem that covers both call and non-call cases uniformly
(with a `LENGTH s'.contexts = LENGTH s.contexts` hypothesis instead
of `¬is_call`) would:

- Simplify the main `step_preserves_non_accessed_storage` proof in
  `vfmRunCall`
- Eliminate the separate `is_call_same_frame_preserves_storage` lemma
- Make the codebase more robust when new call-family opcodes are added

## 5. `active_rollbacks` Definition Could Be Strengthened/Simplified

In `vfmRunCall`:
```
active_rollbacks es_depth s =
  s.rollback ::
  (if LENGTH s.contexts < es_depth then []
   else MAP SND (TAKE (MIN (LENGTH s.contexts - es_depth + 1)
                            (LENGTH s.contexts - 1)) s.contexts))
```

The `MIN` is there to exclude the LAST context's saved rollback
(which `set_original` in `proceed_create` can corrupt). But:

- The MIN formulation obscures the invariant: we want *all* saved
  rollbacks of contexts pushed at or above `es_depth`, *excluding*
  the bottom-most one.
- In the only case where `run_call_inv` is used, `es_depth ≥ 1` and
  `LENGTH s.contexts ≥ es_depth`. The `LENGTH s.contexts < es_depth`
  branch is dead code for the invariant.
- A clearer formulation would be: `MAP SND (FRONT (DROP (es_depth - 1)
  s.contexts))`, making the "exclude LAST" and "start from es_depth"
  structure explicit.

Even better: the reason the LAST rollback is excluded is that
`set_original` modifies it. This suggests that the correct invariant
is not "exclude last" but rather "the LAST rollback satisfies
storage_slot_preserved *modulo set_original effects*". A stronger
invariant that tracks what `set_original` does (it replaces one
account with `empty_account_state` at a known address) would close
the gap and let the invariant include the LAST rollback, simplifying
the MIN logic.

## 6. `decreases_gas` Composition Rules Are Overly Proliferated

The `decreases_gas` predicate has a `strict` boolean parameter,
leading to 7 bind variants: `decreases_gas_bind`,
`decreases_gas_bind_pred`, `decreases_gas_bind_mono`,
`decreases_gas_bind_right`, `decreases_gas_bind_false`, plus
corresponding ignore_bind variants. This is hard to navigate.

A cleaner factoring: separate the "non-strict" (monotone) and
"strict" (strictly-decreasing) properties into two predicates. The
non-strict version composes cleanly. The strict version is a
strengthening that applies only at `consume_gas` calls. This would
reduce to ~3 composition lemmas instead of 7.

## 7. `computes_minimal_domain` and `ignores_extra_domain` — Unrelated But Overlapping

These two predicates in `vfmDomainCollection` and
`vfmDomainSeparation` express related but independent concepts about
domain-aware computation:

- `computes_minimal_domain`: In Collect mode, the domain grows
  minimally; in Enforce mode, if the Enforced domain is insufficient,
  an OutsideDomain error is produced.
- `ignores_extra_domain`: In Enforce mode, the computation is
  insensitive to domain extension beyond what it needs.

These are **dual** perspectives on the same property. A computation
that "computes the minimal domain" automatically "ignores extra domain"
(extending an Enforce domain that already covers the minimal
collection makes no difference). Making this relationship formal would:

- Let `ignores_extra_domain` lemmas be derived from
  `computes_minimal_domain` lemmas
- Halve the number of per-primitive domain lemmas

## 8. `step_inst_inr_preserves_storage` Should Be Nearly Trivial

The theorem states that if `step_inst` returns INR, storage is
preserved. The proof in `vfmStoragePredicates` is long and case-heavy,
but the key observation is simple: **`write_storage` is the only
primitive that modifies `accounts.storage`, and `write_storage` always
returns INL**. Therefore any INR result means `write_storage` was
never reached. Making this observation formal (as a theorem about
`write_storage` always returning INL) would collapse the 50+ line
proof into a 3-line argument.

## 9. Precompile Lemma Explosion

Each monadic predicate theory has ~17 precompile lemmas (one per
precompile), all with identical proof structure. For
`preserves_same_frame`: 17 lemmas, each `rw[def]; irule
preserves_same_frame_bind; rw[]; ...`. For `preserves_txParams`: 17
more. For `preserves_rollback`: 17 more. For `decreases_gas`: 10+
more. For `ignores_extra_domain`: presumably 17 more. For
`computes_minimal_domain`: bundled into a single conjunction. Total:
**~100+ precompile lemmas**.

A generic "precompile preservation" metatheorem could be proved once
per predicate:

```
preserves_property (dispatch_precompiles a) ⇔ T
```

provided all precompiles have the property. This would fold 17 leaf
lemmas into 1 per predicate, or even 1 total if the generic framework
is adopted.

## 10. `same_frame_rel` Doesn't Track `gasUsed` Directly

`same_frame_rel` says the head context's `msgParams` is preserved
(which includes `gasLimit`), but says nothing about `gasUsed`. The
`decreases_gas` predicate has to be tracked entirely separately. If
`same_frame_rel` included the constraint `c.gasUsed ≤ c'.gasUsed`
(for the head context), then `decreases_gas F` for same-frame
operations would follow directly. This would trade a small amount of
generality (some operations like `unuse_gas` decrease gasUsed) for a
significant reduction in proof bookkeeping. Alternatively, a separate
`gas_monotone_rel` could be combined with `same_frame_rel` in a
product relation.

## 11. `outputTo_consistent` Needs To Move Earlier

`outputTo_consistent` is defined in `vfmSameFrame` for the head
context only. `vfmRunCall` then defines
`outputTo_consistent_ctx_def` and `outputTo_consistent_stack_def`
(per-context and per-stack versions). Since the per-context version is
the natural one and the head-only version is just a special case, the
stack-level definitions should be in `vfmSameFrame`. This would let
`vfmHandleStep` and other intermediate theories use the stronger
version, potentially simplifying proofs that currently work around the
head-only limitation.

## 12. `vfmRunCall`'s `proceed_call_pushed_rb_storage` Proof Is Needlessly Manual

The ~80-line proof in `vfmRunCall` for
`proceed_call_pushed_rb_storage` unfolds `proceed_call_def` step by
step, manually threading through each monadic bind. But the primitives
involved (`get_rollback`, `get_current_context`, `read_memory`,
`update_accounts (transfer_value ...)`, `push_context`, etc.) all have
`preserves_storage` or `preserves_rollback` lemmas proved in
`vfmStoragePredicates`. The proof should be a 5-line composition using
those lemmas. The fact that it isn't suggests the composition
framework is not being used at the right level of abstraction.

The same applies to `proceed_create_pushed_rb_storage` and
`proceed_call_push_structure`.

## 13. Priority Ranking

**High impact** (would eliminate hundreds of lemmas and thousands of
lines):

1. Create a generic monadic-predicate framework and instantiate it for
   each property
2. Prove `preserves_same_frame ⇒ cp`,
   `preserves_same_frame ⇒ preserves_rollback ⇒ preserves_storage ⇒ pns`,
   and `preserves_same_frame ⇒ access_monotone`, then derive weaker
   predicate lemmas from stronger ones
3. Collapse `ignores_extra_domain` and `computes_minimal_domain`
   per-primitive lemmas by proving their duality

**Medium impact** (would simplify and strengthen key proofs):

4. Strengthen `step_inst_preserves_non_accessed_storage` to cover
   call-family same-frame aborts
5. Prove `write_storage` always returns INL, then simplify
   `step_inst_inr_preserves_storage`
6. Move `outputTo_consistent_stack` to `vfmSameFrame`
7. Simplify `active_rollbacks` definition and make the invariant
   include the LAST rollback properly

**Lower impact** (would improve maintainability):

8. Collapse precompile lemma families into single dispatch theorems
   per predicate
9. Simplify `decreases_gas` composition API by splitting
   strict/non-strict
10. Make `proceed_call_pushed_rb_storage` etc. use the compositional
    framework rather than manual unfolds

---

## Appendix: Theory Dependency Graph (Simplified)

```
vfmExecutionProp
  ├── vfmStaticCalls (cp)
  ├── vfmTxParams (preserves_txParams)
  ├── vfmDomainSeparation (subdomain, domain_compatible, ignores_extra_domain)
  │   └── vfmDomainCollection (computes_minimal_domain)
  ├── vfmDecreasesGas (decreases_gas)
  ├── vfmStoragePredicates (preserves_rollback, preserves_storage, access_monotone, pns)
  └── vfmSameFrame (same_frame_rel, preserves_same_frame, psf, outputTo_consistent)
      ├── vfmMsdomainPreserved (SND_handle_step_msdomain)
      ├── vfmStepLength (same_frame_or_grow, length_preserves)
      ├── vfmHandleStep (psf_handle_create, handle_exception_same_frame)
      ├── vfmJumpDest (preserves_jumpDest, preserves_all_jumpDest_NONE)
      └── vfmRunWithinFrame (run_within_frame_preserves_*)
          └── vfmRunCall (run_call_inv, run_call_preserves_storage_outside_accessed_slots)

vfmCompute (cv translation, standalone)
```
