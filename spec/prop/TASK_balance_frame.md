# TASK: run_call never lowers a foreign account's balance (rely form)

## Meta
Status: planned
Priority: P1
Created: 2026-11-03
Location: spec/prop

## Theorem Statement (FROZEN)

```sml
Definition foreign_balance_change_def:
  foreign_balance_change acc acc' ⇔
    foreign_account_change acc acc' ∧ acc.balance ≤ acc'.balance
End

Theorem run_call_account_balance_frame:
  wf_state es ∧
  (∀acc acc'. P acc ∧ foreign_balance_change acc acc' ⇒ P acc') ∧
  P (lookup_account a es.rollback.accounts) ∧
  (2 ≤ LENGTH es.contexts ⇒
     P (lookup_account a (SND (HD es.contexts)).accounts)) ∧
  (∀e r e'.
     (FST (HD e.contexts)).msgParams.callee = a ∧
     wf_state e ∧ P (lookup_account a e.rollback.accounts) ∧
     (2 ≤ LENGTH e.contexts ⇒
        P (lookup_account a (SND (HD e.contexts)).accounts)) ∧
     (e = es ∨
      ∃s u. run_call_reaches es s ∧
            LENGTH es.contexts ≤ LENGTH s.contexts ∧
            wf_state s ∧
            (FST (HD s.contexts)).msgParams.callee ≠ a ∧
            P (lookup_account a s.rollback.accounts) ∧
            step s = (INL u, e) ∧
            LENGTH s.contexts < LENGTH e.contexts ∧
            ¬(FST (HD e.contexts)).msgParams.static) ∧
     run_call e = SOME (r, e') ⇒
     P (lookup_account a e'.rollback.accounts)) ∧
  run_call es = SOME (r, es') ⇒
  P (lookup_account a es'.rollback.accounts)
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.
Do not change `foreign_account_change_def` or the statement of any existing
non-`[local]` theorem in this file or elsewhere; add new theorems instead.
Existing `[local]` helpers may be generalized.

## Completion Criteria

1. `holbuild -j4 build vfmAccountFrameTheory` passes with zero CHEAT warnings and zero FAILs.
2. No duplicate or near-duplicate lemmas — each helper exists once in its most general form.

**If the theorem is false as stated:**
- Produce a counterexample (the concrete step that lowers a foreign account's balance).
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holbuild -j4 build vfmAccountFrameTheory
```
(run from the project root, the directory with holproject.toml)

## Background

`run_call_account_frame` (same file) is the rely form of the per-account
frame: if every frame entered as account `a` preserves a predicate `P` of
`a`'s account, then `run_call` preserves `P`, provided `P` is closed under
`foreign_account_change` (what a frame not executing as `a` can do to it).
That relation leaves the balance free, so `P` cannot mention `a`'s balance.
Consumers proving solvency (`a`'s balance ≥ some stored total) need a version
where foreign changes may only keep or raise `a`'s balance. That is true of
the EVM: value leaves an account only from a frame executing as it
(CALL/CREATE value via `transfer_value` from the callee, SELFDESTRUCT of the
callee); a reverting pop restores the frame's snapshot, which the existing
proof already handles through the invariant that `P` holds of every active
snapshot (`active_rollbacks`). A statement check found no counterexample:
the push snapshot is read before the value transfer (`proceed_call`,
`spec/vfmExecutionScript.sml` ~1491), precompiles write no accounts, a
successful pop only deposits code at the child's callee.

## Domain Constraints

- Keep the default tactic timeout; never set `tactic_timeout` or pass `--tactic-timeout`.
- No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`.
- No new axioms, no cheats.
- New helper theorems go in this theory (`spec/prop/vfmAccountFrameScript.sml`) or, if they
  belong with the same-frame relation, in `spec/prop/vfmSameFrameScript.sml` as new theorems.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Target theory | spec/prop/vfmAccountFrameScript.sml | `run_call_account_frame` (~line 2502) and its step lemmas `step_same_frame_foreign`, `step_push_foreign`, `step_pop_foreign`, `step_foreign_account_invariant`, `active_rollbacks_*`, `run_call_foreign_trace` |
| Same-frame relation | spec/prop/vfmSameFrameScript.sml | `callee_local_changes`, `same_frame_rel`, `step_same_frame` |
| EVM semantics | spec/vfmExecutionScript.sml | `step`, `proceed_call`, `proceed_create`, `step_self_destruct`, `transfer_value`, `handle_step`, `pop_and_incorporate_context`, `dispatch_precompiles` |
| State types | spec/vfmStateScript.sml, spec/vfmContextScript.sml | accounts, `lookup_account`, `update_account` |
| Other props | spec/prop/ | `vfmRunCall`, `vfmHandleStep`, `vfmStepLength`, `vfmPreserves`, `vfmStaticCalls` |

## Notes

The new theorem's proof is expected to follow `run_call_account_frame`'s,
with balance monotonicity added to the foreign-step facts.
