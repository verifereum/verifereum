# TASK: run_call frame law over an account and its transient storage

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: spec/prop/vfmAccountFrameScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

```sml
Theorem run_call_account_transient_frame:
  wf_state es ∧
  (∀acc acc' ts. P (acc, ts) ∧ foreign_account_change acc acc' ⇒
                 P (acc', ts)) ∧
  P (lookup_account a es.rollback.accounts, es.rollback.tStorage a) ∧
  (2 ≤ LENGTH es.contexts ⇒
     P (lookup_account a (SND (HD es.contexts)).accounts,
        (SND (HD es.contexts)).tStorage a)) ∧
  (∀e r e'.
     (FST (HD e.contexts)).msgParams.callee = a ∧
     wf_state e ∧
     P (lookup_account a e.rollback.accounts, e.rollback.tStorage a) ∧
     (2 ≤ LENGTH e.contexts ⇒
        P (lookup_account a (SND (HD e.contexts)).accounts,
           (SND (HD e.contexts)).tStorage a)) ∧
     (e = es ∨
      ∃s u. run_call_reaches es s ∧
            LENGTH es.contexts ≤ LENGTH s.contexts ∧
            wf_state s ∧
            (FST (HD s.contexts)).msgParams.callee ≠ a ∧
            P (lookup_account a s.rollback.accounts, s.rollback.tStorage a) ∧
            step s = (INL u, e) ∧
            LENGTH s.contexts < LENGTH e.contexts ∧
            ¬(FST (HD e.contexts)).msgParams.static) ∧
     run_call e = SOME (r, e') ⇒
     P (lookup_account a e'.rollback.accounts, e'.rollback.tStorage a)) ∧
  run_call es = SOME (r, es') ⇒
  P (lookup_account a es'.rollback.accounts, es'.rollback.tStorage a)
```

Supporting definitions (all already in the repo): `foreign_account_change_def`,
`run_call_reaches_def` (spec/prop/vfmAccountFrameScript.sml), `run_call_def`,
`active_rollbacks_def` (spec/prop/vfmRunCallScript.sml), `wf_state_def`.

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build vfmAccountFrameTheory` passes with zero CHEAT warnings and zero FAILs, at the default 2.5 s per-step tactic timeout.
2. No duplicate or near-duplicate lemmas: each helper exists once in its most general form. Where an existing lemma of `vfmAccountFrameScript.sml` is the accounts-only special case of what you need, generalise it (see Domain Constraints) rather than copying it with tStorage added.
3. Every theorem of `vfmAccountFrameScript.sml` that is not `[local]` keeps its exact statement and name (its proof may change, e.g. to derive it from a more general new lemma). This includes `run_call_account_frame`, `run_call_account_balance_frame`, `run_call_foreign_trace`, `step_same_frame_foreign`, `step_push_foreign`, `step_pop_foreign`, `step_pop_foreign_balance`, `run_call_static_frame` and all the `*_invariant` lemmas.

**If the theorem is false as stated:**
- Produce a concrete counterexample scenario.
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holbuild -j4 build vfmAccountFrameTheory
```

## Background

verifereum is an executable EVM semantics in HOL4. `run_call es` runs the
current call frame of `es` (and every frame it calls) until it returns.
`run_call_account_frame` is a rely/guarantee frame law: if every frame entered
as account `a` preserves a predicate P of `a`'s account record, then the whole
run preserves P, because frames not executing as `a` only make a
`foreign_account_change` to it. A downstream proof (Vyper contract invariants)
needs the same law where P also reads `a`'s transient storage (EIP-1153,
`rollback.tStorage a`), because its invariant spans both storage backends.
The new theorem is that companion: same rely form, P on the pair.

`run_call_account_balance_frame` is proved through the `[local]` trace lemma
`run_call_foreign_balance_trace` and the step lemmas
`step_same_frame_foreign`, `step_push_foreign`/`step_push_balance`,
`step_pop_foreign_balance`, the `*_invariant` lemmas over `active_rollbacks`,
and `run_call_static_frame` for static pushes into `a`. The new theorem needs
the same chain with `tStorage a` carried along, plus the fact that a static
frame (and everything it calls) leaves `rollback.tStorage` unchanged.

## Domain Constraints

- HOL4 under holbuild; use `Theorem … Proof … QED`. No `cheat`, no new axioms.
- holbuild's default per-step tactic timeout (2.5 s) holds; never raise it or add `tactic_timeout` to holproject.toml. A step that runs over is a proof performance bug: split the step or cut the rewrite set.
- Never wrap `metis_tac` or other search in `TRY`/`ORELSE`; select goals with `>~`, `>-`, `>|`.
- No `let` in theorem statements.
- Statements of non-`[local]` theorems stay byte-for-byte as they are (Completion Criteria 3). `[local]` helpers may be restated or generalised freely; adding new exported lemmas is fine.
- Prefer existing definitions; a new definition (for example a relation over rollback states) is allowed if it makes the generalisation clean, but keep it minimal and give it a comment.
- Keep the work in `spec/prop/vfmAccountFrameScript.sml` unless a lemma clearly belongs in an ancestor theory next to its definitions.
- Do not run EEST or other test suites.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Target file | `spec/prop/vfmAccountFrameScript.sml` | the frozen theorem sits right after `run_call_account_frame`; the whole existing accounts-only proof chain is in this file |
| Same-frame relation | `spec/prop/vfmSameFrameScript.sml` | `callee_local_changes_def` already includes `∀a. a ≠ callee ⇒ r'.tStorage a = r.tStorage a`; `same_frame_rel_def`, `step_same_frame` |
| Static frames | `spec/prop/vfmStaticCallsScript.sml` | `static_inv` (tracks accounts, tStorage, toDelete for all-static stacks), cp lemmas |
| run_call, active_rollbacks | `spec/prop/vfmRunCallScript.sml` | `run_call_def`, `active_rollbacks_def`, `active_rollbacks_saved` |
| Within-frame | `spec/prop/vfmRunWithinFrameScript.sml` | `run_within_frame_preserves_tStorage_outside_callee` |
| Preservation combinators | `spec/prop/vfmPreservesScript.sml`, `spec/prop/vfmStoragePredicatesScript.sml` | `preserves_when`, bind/cp lemmas |
| Semantics | `spec/vfmExecutionScript.sml` | `step_def`, `step_inst_def` (TStore: `assert_not_static`, `set_tStorage`), `proceed_call_def`, `proceed_create_def`, `pop_and_incorporate_context_def` (failure: `set_rollback (SND callee_rb)`), `handle_create_def`, `handle_exception_def` |
| State/context | `spec/vfmStateScript.sml`, `spec/vfmContextScript.sml` | `rollback_state` (fields accounts, tStorage, accesses, toDelete), `lookup_account`, `wf_state` |
| Build logs | `.holbuild/logs/current/verifereum/vfmAccountFrameTheory/build.log` | (read via holbuild tool output) |

## Notes

The statement was checked by hand against the semantics: TSTORE writes only the executing callee's transient storage and fails in static frames; pushes and value transfers never write tStorage; a failed pop restores the whole saved rollback.
