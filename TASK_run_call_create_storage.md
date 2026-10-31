# TASK: run_call storage frame with CREATE clearing storage

## Meta
Status: planned
Priority: P1
Created: 2026-10-31
Location: spec/prop (verifereum, this worktree)

## Theorem Statement (FROZEN)

All of the following, exactly as they now stand in the scripts. Do not
modify these statements. Prove each as-is, or produce a counterexample.

In `spec/prop/vfmStoragePredicatesScript.sml`:

```sml
Theorem step_create_storage:
  step_create two s = (r, s') ⇒
  ∀a k.
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage ∨
    r = INL () ∧ LENGTH s'.contexts = SUC (LENGTH s.contexts) ∧
    lookup_storage k (lookup_account a s'.rollback.accounts).storage = 0w ∧
    ¬account_already_created (lookup_account a s.rollback.accounts)
```

In `spec/prop/vfmRunCallScript.sml`:

```sml
Theorem step_preserves_non_accessed_storage:
  ∀s r s'. step s = (r, s') ∧ s.contexts ≠ [] ∧
    outputTo_consistent s ∧
    same_frame_rel s s' ⇒
  ∀a k. ¬fIN (SK a k) s'.rollback.accesses.storageKeys ⇒
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage

Theorem step_push_structure:   (* the whole statement as in the file; only
                                  its second conjunct changed, to: *)
    (∀a. (lookup_account a s'.rollback.accounts).storage =
         (lookup_account a s.rollback.accounts).storage ∨
         (lookup_account a s'.rollback.accounts).storage = empty_storage ∧
         ¬account_already_created (lookup_account a s.rollback.accounts)) ∧

Theorem run_call_preserves_storage_outside_accessed_slots:
  ∀es r es'.
    wf_state es ∧
    (FST(HD es.contexts)).jumpDest = NONE ∧
    EVERY (λrb. storage_slot_preserved rb es.rollback)
          (MAP SND (TAKE 2 es.contexts)) ∧
    run_call es = SOME (r, es') ⇒
    ∀a k. ¬fIN (SK a k) es'.rollback.accesses.storageKeys ⇒
        lookup_storage k (lookup_account a es'.rollback.accounts).storage =
        lookup_storage k (lookup_account a es.rollback.accounts).storage ∨
        lookup_storage k (lookup_account a es'.rollback.accounts).storage = 0w ∧
        ¬account_already_created (lookup_account a es.rollback.accounts)

Theorem run_call_preserves_txParams:  (* as in the file, unchanged *)
Theorem run_call_preserves_storage_outside_accessed_slots_single:  (* as in the file *)
Theorem run_call_preserves_storage_outside_accessed_slots_initial: (* as in the file *)
Theorem run_call_preserves_txParams_single:  (* as in the file, unchanged *)
```

Supporting definitions (do not change any of these):

```sml
Definition account_already_created_def:   (* spec/vfmExecutionScript.sml *)
  account_already_created a = ¬(a.nonce = 0 ∧ NULL a.code)
End
Definition clear_storage_def:   (* spec/vfmExecutionScript.sml *)
  clear_storage address accounts =
  let account = lookup_account address accounts in
    update_account address (account with storage := empty_storage) accounts
End
(* spec/prop/vfmRunCallScript.sml *)
Definition storage_slot_preserved_def: ...   (* unchanged *)
Definition active_rollbacks_def: ...         (* unchanged *)
```

`run_call_inv_def`, `run_call_inv_refl`, `run_call_inv_step` and
`run_call_preserves_inv` are NOT frozen: they are internal to
vfmRunCallScript.sml and may be restated, weakened or replaced. (The
invariant as defined is now false; see the comment above
`run_call_inv_def`.)

(*
 ************************************************************
 * DO NOT START THIS PROOF until you have finished and
 * validated ALL the machinery you will need for it.
 * Building generic lemmas that help IS in scope.
 ************************************************************
 *)

## Completion Criteria

1. `holbuild -j4 build verifereumTheory` passes, and the logs of that build
   show no CHEAT in vfmStoragePredicatesTheory, vfmRunCallTheory or any
   theory after them.
2. No `cheat` left in spec/prop/vfmStoragePredicatesScript.sml or
   spec/prop/vfmRunCallScript.sml. The commented-out original proofs above
   the current cheats are removed once the theorem is proved.
3. No duplicate or near-duplicate lemmas.
4. No change to any frozen statement, nor to any definition outside
   vfmRunCallScript.sml's run_call_inv.

**If a statement is false as stated:**
- Produce a HOL4 counterexample.
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
cd <this worktree root>   # the directory holding holproject.toml
holbuild -j4 build verifereumTheory
```

Single theories: `holbuild -j4 build vfmStoragePredicatesTheory`,
`holbuild -j4 build vfmRunCallTheory`.

## Background

verifereum is an executable EVM semantics. CREATE (both the opcode,
`step_create`/`proceed_create`, and a creation transaction,
`run_create`) used to refuse an address with nonzero nonce, code, or
nonempty storage. It now follows the Ethereum execution spec (EELS
Osaka): only nonce and code make a collision, and creating into an
address with leftover storage clears that storage first
(`clear_storage`, applied in `proceed_create` before the nonce and value
updates). The storage-frame theorems used to say every slot outside the
accessed storageKeys is unchanged; with clearing, a slot can also become
0 when its account had nonce 0 and no code. The frozen statements say
exactly that. The commented-out original proofs above each cheat show
how the pre-change versions were proved; they used
`preserves_storage_step_create`, which is gone (it is false now) and was
replaced by `step_create_storage` and `proceed_create_storage`.

## Domain Constraints

- Tactic timeout is holbuild's default 2.5 s per step. Never raise it
  (no `tactic_timeout`, no `--tactic-timeout`). Split slow steps.
- Never wrap metis_tac or another search in `TRY` or `ORELSE`; select
  goals with `>~`, `>-`, `>|`.
- No `cheat`, no new axioms, no new hypotheses on frozen statements.
- No `let` in theorem statements.
- Use holbuild only (no Holmake).
- Other theories (vfmAccountFrame, vfmAccountDeletion, ...) use
  `step_push_structure` by conjunct number (`cj 1`, `cj 6`, `cj 10`);
  keep its conjunct order.
- Commits: one commit per milestone that builds, on the current branch,
  touching only the .sml files you changed (never commit PLAN_, STATE_,
  LEARNINGS_, LOG_, FOCUS_ files or .alan/). End each commit message with
  these two lines exactly:
  `Bot: opus (Claude Opus 5.5)`
  `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`
  Never push.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Semantics | spec/vfmExecutionScript.sml | step_create, proceed_create, clear_storage, account_already_created, run_create |
| Storage lemmas | spec/prop/vfmStoragePredicatesScript.sml | preserves_storage combinators, proceed_create_storage (proved), step_create_storage (cheat) |
| run_call frame | spec/prop/vfmRunCallScript.sml | run_call_inv, active_rollbacks, step_push_structure, the frozen corollaries |
| CREATE path lemma | spec/prop/vfmAccountFrameScript.sml | step_create_reaches_proceed_create, proceed_create_frame_effects (downstream of RunCall; read for ideas, don't import) |
| Same-frame | spec/prop/vfmSameFrameScript.sml | same_frame_rel, callee_local_changes |
| Step structure | spec/prop/vfmHandleStepScript.sml, vfmStepLengthScript.sml | step/handle decomposition, length facts |
| Nonce monotonicity | spec/prop/vfmExecutionPropScript.sml, vfmAccountDeletionScript.sml | wf_accounts, nonce facts (grep `nonce`) |
| Built theory sigs | .holbuild/ (grep the .sig files) | everything in scope |
