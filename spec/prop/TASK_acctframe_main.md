# TASK: Per-account rely for run_call

## Meta
Status: planned
Priority: P0
Created: 2026-10-24
Location: spec/prop/

## Theorem Statement (FROZEN)

```sml
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
```

Supporting definitions (in spec/prop/vfmAccountFrameScript.sml):

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
2. Do not change any other theorem's statement or any definition in the repo. Other theorems in vfmAccountFrameScript.sml whose proofs are `cheat` are being proved separately; you may use their statements as lemmas, and you must not edit their proofs.
3. Helper lemmas go in spec/prop/vfmAccountFrameScript.sml (above their first use), or in the theory where they belong if they are general facts about an existing definition (but do not edit other theories' existing statements). No duplicates of existing lemmas: search first.
4. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`. Every proof step must run within the project's tactic timeout; split slow steps rather than raising any timeout. No new axioms, no `cheat`.

**If a frozen theorem is false as stated:** produce a concrete counterexample scenario (which opcode / path / field), state the tightest sufficient fix, and stop. Do NOT silently weaken the statement.

## Build

```
cd /home/claude/workspace/verifereum/.claude/worktrees/acctframe-main
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
