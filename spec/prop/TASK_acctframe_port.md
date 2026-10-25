# TASK: Repair vfmAccountFrame after the original-accounts refactor

## Meta
Status: planned
Priority: P0
Created: 2026-10-25
Location: spec/prop/

## Theorem Statement (FROZEN)

All of these were fully proved (no cheats) before upstream main changed under them. Every proof in spec/prop/vfmAccountFrameScript.sml must build again.

```sml
Theorem run_call_reaches_inv:
  Q es ∧
  (∀s u s'. Q s ∧ LENGTH es.contexts ≤ LENGTH s.contexts ∧
            step s = (INL u, s') ⇒ Q s') ∧
  run_call_reaches es s ⇒
  Q s

Theorem OWHILE_RTC:
  ∀x y. RTC (λx y. G x ∧ f x = y) x y ⇒ OWHILE G f x = OWHILE G f y

Theorem step_same_frame_foreign:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s'.contexts = LENGTH s.contexts ⇒
  TL s'.contexts = TL s.contexts ∧
  SND (HD s'.contexts) = SND (HD s.contexts) ∧
  (FST (HD s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams ∧
  ∀y. y ≠ (FST (HD s.contexts)).msgParams.callee ⇒
      foreign_account_change (lookup_account y s.rollback.accounts)
                             (lookup_account y s'.rollback.accounts)

Theorem step_push_foreign:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s.contexts < LENGTH s'.contexts ⇒
  ISL r ∧
  LENGTH s'.contexts = SUC (LENGTH s.contexts) ∧
  MAP FST (TL (TL s'.contexts)) = MAP FST (TL s.contexts) ∧
  FRONT (TL (TL s'.contexts)) = FRONT (TL s.contexts) ∧
  (FST (EL 1 s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams ∧
  (2 ≤ LENGTH s.contexts ⇒ SND (EL 1 s'.contexts) = SND (HD s.contexts)) ∧
  ∀y. y ≠ (FST (HD s.contexts)).msgParams.callee ⇒
      foreign_account_change (lookup_account y s.rollback.accounts)
                             (lookup_account y s'.rollback.accounts) ∧
      foreign_account_change (lookup_account y s.rollback.accounts)
                             (lookup_account y (SND (HD s'.contexts)).accounts)

Theorem step_push_new_frame:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s.contexts < LENGTH s'.contexts ∧
  (FST (HD s'.contexts)).msgParams.callee ≠
    (FST (HD s.contexts)).msgParams.callee ⇒
  ∃code static rd t.
    FST (HD s'.contexts) =
      initial_context (FST (HD s'.contexts)).msgParams.callee
        code static rd t ∧
    ((∃mr. rd = Memory mr) ∧
     code =
       (case get_delegate
               (lookup_account (FST (HD s'.contexts)).msgParams.callee
                  s.rollback.accounts).code of
          NONE => (lookup_account (FST (HD s'.contexts)).msgParams.callee
                     s.rollback.accounts).code
        | SOME d => (lookup_account d s.rollback.accounts).code) ∧
     (FST (HD s'.contexts)).msgParams.caller =
       (FST (HD s.contexts)).msgParams.callee ∧
     (FST (HD s'.contexts)).msgParams.value ≤
       (lookup_account (FST (HD s.contexts)).msgParams.callee
          s.rollback.accounts).balance ∧
     s'.rollback.accounts =
       transfer_value (FST (HD s.contexts)).msgParams.callee
         (FST (HD s'.contexts)).msgParams.callee
         (FST (HD s'.contexts)).msgParams.value s.rollback.accounts ∧
     s'.rollback.tStorage = s.rollback.tStorage ∨
     rd = Code (FST (HD s'.contexts)).msgParams.callee ∧
     ¬account_already_created
        (lookup_account (FST (HD s'.contexts)).msgParams.callee
           s.rollback.accounts)) ∧
    (static ⇒ (∃mr. rd = Memory mr) ∧
              (SND (HD s'.contexts)).accounts = s'.rollback.accounts)

Theorem step_pop_foreign:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s'.contexts < LENGTH s.contexts ⇒
  ∃new_head parent rest.
    s.contexts = HD s.contexts :: parent :: rest ∧
    s'.contexts = (new_head, SND parent) :: rest ∧
    new_head.msgParams = (FST parent).msgParams ∧
    (s'.rollback.accounts = (SND (HD s.contexts)).accounts ∨
     ∀y. y ≠ (FST (HD s.contexts)).msgParams.callee ⇒
         foreign_account_change (lookup_account y s.rollback.accounts)
                                (lookup_account y s'.rollback.accounts))

Theorem run_call_static_frame:
  wf_state e ∧
  (FST (HD e.contexts)).msgParams.static ∧
  (∀x. (FST (HD e.contexts)).msgParams.outputTo ≠ Code x) ∧
  (SND (HD e.contexts)).accounts = e.rollback.accounts ∧
  run_call e = SOME (r, e') ⇒
  e'.rollback.accounts = e.rollback.accounts

Theorem run_call_account_frame:
  wf_state es ∧
  (∀acc acc'. P acc ∧ foreign_account_change acc acc' ⇒ P acc') ∧
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

Theorem run_call_empty_code_frame:
  wf_state e ∧
  (FST (HD e.contexts)).msgParams.code = [] ∧
  (lookup_account (FST (HD e.contexts)).msgParams.callee
     e.rollback.accounts).code = [] ∧
  run_call e = SOME (r, e') ⇒
  e'.rollback.accounts = e.rollback.accounts

Theorem run_call_empty_code_account:
  wf_state es ∧
  (lookup_account a es.rollback.accounts).code = [] ∧
  account_already_created (lookup_account a es.rollback.accounts) ∧
  (2 ≤ LENGTH es.contexts ⇒
     (lookup_account a (SND (HD es.contexts)).accounts).code = [] ∧
     (lookup_account a (SND (HD es.contexts)).accounts).storage =
       (lookup_account a es.rollback.accounts).storage ∧
     account_already_created
       (lookup_account a (SND (HD es.contexts)).accounts)) ∧
  ((FST (HD es.contexts)).msgParams.callee = a ⇒
     (FST (HD es.contexts)).msgParams.code = []) ∧
  run_call es = SOME (r, es') ⇒
  (lookup_account a es'.rollback.accounts).code = [] ∧
  (lookup_account a es'.rollback.accounts).storage =
    (lookup_account a es.rollback.accounts).storage

Theorem step_storage_keys_foreign:
  wf_state s ∧ step s = (r, s') ∧
  y ≠ (FST (HD s.contexts)).msgParams.callee ∧
  fIN (SK y k) s'.rollback.accesses.storageKeys ⇒
  fIN (SK y k) s.rollback.accesses.storageKeys ∨
  LENGTH s'.contexts < LENGTH s.contexts ∧
  fIN (SK y k) (SND (HD s.contexts)).accesses.storageKeys

Theorem step_push_storage_keys:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s.contexts < LENGTH s'.contexts ⇒
  s'.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys ∧
  (SND (HD s'.contexts)).accesses.storageKeys =
    s.rollback.accesses.storageKeys

Theorem run_call_storage_key_added:
  wf_state es ∧
  (2 ≤ LENGTH es.contexts ⇒
     ¬fIN (SK a k) (SND (HD es.contexts)).accesses.storageKeys) ∧
  run_call es = SOME (r, es') ∧
  fIN (SK a k) es'.rollback.accesses.storageKeys ∧
  ¬fIN (SK a k) es.rollback.accesses.storageKeys ⇒
  ∃s u s'.
    run_call_reaches es s ∧ LENGTH es.contexts ≤ LENGTH s.contexts ∧
    (FST (HD s.contexts)).msgParams.callee = a ∧
    step s = (u, s') ∧
    ¬fIN (SK a k) s.rollback.accesses.storageKeys ∧
    fIN (SK a k) s'.rollback.accesses.storageKeys
```

```sml
Definition foreign_account_change_def:
  foreign_account_change acc acc' ⇔
    acc'.code = acc.code ∧ acc'.storage = acc.storage ∧
    (acc'.nonce = acc.nonce ∨ ¬account_already_created acc)
End

Definition run_call_reaches_def:
  run_call_reaches es s ⇔
    RTC (λs1 s2. LENGTH es.contexts ≤ LENGTH s1.contexts ∧
                 ∃u. step s1 = (INL u, s2)) es s
End
```

**Do not modify these statements.** Prove them as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build vfmAccountFrameTheory` (from the project root) builds with no CHEAT for the frozen theorem(s) above, and no FAIL.
2. Do not change any definition in the repo, or any theorem statement outside vfmAccountFrameScript.sml. Inside it, the frozen theorems and definitions above keep their exact statements; other helper lemmas there may be restated, replaced or deleted as the repair needs.
3. Helper lemmas go in spec/prop/vfmAccountFrameScript.sml (above their first use), or in the theory where they belong if they are general facts about an existing definition (but do not edit other theories' existing statements). No duplicates of existing lemmas: search first.
4. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`. Every proof step must run within the project's tactic timeout; split slow steps rather than raising any timeout. No new axioms, no `cheat`.

**If a frozen theorem is false as stated:** produce a concrete counterexample scenario (which opcode / path / field), state the tightest sufficient fix, and stop. Do NOT silently weaken the statement.

## Build

```
cd /home/claude/workspace/verifereum/.claude/worktrees/acctframe-port
holbuild -j2 build vfmAccountFrameTheory
```

## Background

verifereum is an executable EVM semantics (Osaka fork) in HOL4. `step` executes one instruction of the current (head) context in `s.contexts`; `run_call es` iterates `step` while the result is `INL` and the stack is at least as deep as at the start. CALL/CREATE push a context together with a saved rollback (restored if that frame fails); returning pops it (handle_step → handle_create → handle_exception → pop_and_incorporate_context). The goal of vfmAccountFrame is a per-account frame: account `a`'s code and storage change only through frames executing as `a` (context callee `a`).

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Execution semantics | spec/vfmExecutionScript.sml | step, step_inst, step_call, step_create, proceed_call, proceed_create, handle_create, handle_exception, pop_and_incorporate_context, step_self_destruct, step_sstore, step_sload, access_slot, set_original, run_call |
| Contexts | spec/vfmContextScript.sml | initial_context, initial_msg_params, get_delegate, parse_code, precompile_addresses |
| State | spec/vfmStateScript.sml | accounts are functions; lookup_account, update_account, storage |
| Well-formedness | spec/prop/vfmExecutionPropScript.sml | wf_state, wf_context, outputTo_consistent(_stack); step_preserves_nonempty_contexts etc. |
| Generic monadic preservation | spec/prop/vfmPreservesScript.sml | preserves / preserves_when and their bind/handle/cond composition lemmas |
| Same-frame relation | spec/prop/vfmSameFrameScript.sml | same_frame_rel, callee_local_changes, preserves_same_frame (psf) leaves for every primitive, bind_psf_grows_extract, transfer_value_preserves_code/nonce/storage |
| Storage predicates | spec/prop/vfmStoragePredicatesScript.sml | preserves_rollback / preserves_storage / access_monotone / pns frameworks, per-primitive leaves, step_inst_inr_preserves_storage |
| Handle-step lemmas | spec/prop/vfmHandleStepScript.sml | psf_handle_create, handle_exception_pop_generic_gen (s'.rollback = s.rollback ∨ callee_rb), handle_step_pop_generic_gen(_paired), handle_create_preserves_tl_and_snd_hd, handle_step_not_abort_pops, handle_step_shrinks_by_one |
| Within-frame runs | spec/prop/vfmRunWithinFrameScript.sml | step_same_frame (equal length ⇒ same_frame_rel), inr_grow_P / inr_grow_witness_step_call (code/nonce facts on CALL pushes) |
| run_call storage frame | spec/prop/vfmRunCallScript.sml | step_push_structure, step_pop_structure, step_call_push_structure, step_create_push_structure, proceed_call/proceed_create push lemmas, active_rollbacks, run_call_inv and its preservation proof (a model for OWHILE_INV_IND over run_call), step_preserves_wf_state |
| Static calls | spec/prop/vfmStaticCallsScript.sml | static_inv and step_preserves_static_inv / run_static_preserves (whole-stack static case) |
| HOL4 sources | resolved under .holbuild/src/hol/ after a build | WhileTheory (OWHILE_THM, OWHILE_INV_IND), relationTheory (RTC_INDUCT, RTC_RULES_RIGHT1) |

## Domain Constraints

- Build only with holbuild from the project root; do not use Holmake.
- Do not touch tests/, EEST fixtures, or other theories' existing statements.

## Notes

- What changed upstream (merged PR "Separate original accounts from rollback snapshots", commit 5f72e263): `execution_state` gained an `originalAccounts` field. `get_original`/`set_original` now read and write it instead of the accounts of the LAST saved rollback, so CREATE no longer edits any saved rollback. `active_rollbacks`, `all_accounts`, `wf_state`, `same_frame_rel`, `cp`, `cp_rel` and their lemmas in vfmRunCall, vfmSameFrame and vfmExecutionProp changed with it. Read `git show 5f72e263 -- spec/` for the exact changes.
- First failure seen: `active_rollbacks_initial` (a `decide_tac` step). holbuild stops at the first failing theorem, so expect more after it.
- The theory built fully at commit 4b097c75 (before the upstream merge); `git diff 4b097c75 HEAD -- spec/ ':!spec/prop/vfmAccountFrameScript.sml'` shows the upstream changes the file now builds against.
