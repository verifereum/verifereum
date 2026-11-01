# TASK: `pop_and_incorporate_context_all_jumpDest_NONE`

## Meta
Status: planned
Priority: P1
Created: 2026-11-01
Location: the project root (this directory); the SML file is
`spec/prop/vfmJumpDestScript.sml`.

## Theorem Statement (FROZEN)

```sml
Theorem pop_and_incorporate_context_all_jumpDest_NONE[local]:
  pop_and_incorporate_context b s = (r, s') ∧
  EVERY (λc. (FST c).jumpDest = NONE) (TL s.contexts) ⇒
  all_jumpDest_NONE s'
```

Supporting definitions, all already in the tree:

```sml
Definition all_jumpDest_NONE_def: (* spec/prop/vfmJumpDestScript.sml *)
  all_jumpDest_NONE s ⇔ EVERY (λc. (FST c).jumpDest = NONE) s.contexts
End

Definition pop_and_incorporate_context_def: (* spec/vfmExecutionScript.sml *)
  pop_and_incorporate_context success = do
    calleeGasLeft <- get_gas_left;
    callee_rb <- pop_context;
    callee <<- FST callee_rb;
    unuse_gas calleeGasLeft;
    context <- get_current_context;
    set_current_context (absorb_state_gas context callee.stateGasLeft
                           callee.stateGasSpilled callee.stateGasCommitted);
    if success then do
      push_logs callee.logs;
      update_gas_refund (callee.addRefund, callee.subRefund);
      repay_state_gas_spill
    od else do
      ...credit the child's creation charge back to the parent...
    od
  od
End
```

The body of `pop_and_incorporate_context` is in the file; read it there rather
than relying on the sketch above.

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

(*
 ************************************************************
 * DO NOT START THIS PROOF until you have finished and
 * validated ALL the machinery you will need for it.
 * Especially machinery that can be generalized and shared
 * between proofs — write it in separate helper files
 * (e.g. <project>Lib.sml, <project>Script.sml) and build them first.
 *
 * Building generic, powerful abstractions (lemmas, tactics,
 * conversions) that help this proof IS explicitly in scope.
 ************************************************************
 *)

## Completion Criteria

1. `holbuild -j4 build vfmJumpDestTheory` passes with no `cheat`, no
   `mk_thm` and no axiom in the diff, and no CHEAT line in the build log.
2. The frozen statement above is unchanged, byte for byte. No other
   theorem's statement in the tree is changed. Weakening the statement,
   adding a hypothesis or adding a new premise is not a fix; if the
   statement cannot be proved, stop and say so.
3. The only other change to `spec/prop/vfmJumpDestScript.sml` besides a
   real proof for this theorem is the removal of the `cheat` and of the
   `TEMPORARY` comment above it. Anything else you need goes in as an
   ordinary `[local]` helper lemma in the same file.
4. `cheat` appears nowhere in `spec/prop/vfmJumpDestScript.sml` when you
   are done; the neighbouring `pop_and_incorporate_context_then_all_jumpDest_NONE`
   keeps its real proof.

**If the theorem is false as stated:**
- Produce a HOL4 counterexample (e.g. `EVAL_TAC` on concrete values).
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
cd /home/claude/workspace/.worktrees/verifereum-seq58-merge
HOLDIR=/home/claude/.cache/holbuild/hol-toolchains/d33a474b26ab2efef488eeb66cc46abd3bab3f8c/hol \
  holbuild -j4 build vfmJumpDestTheory
```

`holbuild` is the only build tool (never Holmake, never `--holdir`). A plain
build resumes from a theorem-context checkpoint, so re-running is cheap; use
`--skip-checkpoints --force=theory` if you want the proof replayed from the
top, and `--force=theory` after an edit that does not change the file's
dependencies. The project has no `tactic_timeout` override, so the per-step
budget is holbuild's default 2.5s.

## Background

`verifereum` is an executable EVM semantics in HOL4, and
`spec/prop/vfmJumpDestScript.sml` proves that the jump-destination cache is
preserved by the interpreter's steps. `pop_and_incorporate_context` is how a
child frame is merged back into its parent: it pops the child, gives the
child's unused execution gas back to the parent, and merges the child's
refunds and logs.

This branch adds EIP-8037's second gas dimension ("state gas") to the
semantics. The pop now also:

- absorbs the child's state-gas meter into the parent's, through
  `absorb_state_gas` (`spec/vfmExecutionScript.sml`);
- on the failure path, credits the account-creation charge the parent paid
  back through `credit_new_account`, which is a `credit_state_gas_refund
  new_account_state_gas` when the child's `msgParams.newAccountCharged` is
  set.

The lemma's proof as it came from upstream was written for the old pop: it
unfolds `pop_and_incorporate_context` and expects the resulting state to be
the parent frame with `TL` applied to its context list, which it names with
an abbreviation. With the state-gas steps in place the unfolding no longer
produces that shape, so the abbreviation's pattern does not match. The
statement itself is still true: neither `absorb_state_gas`, nor
`set_current_context`, nor `credit_state_gas_refund` writes a `jumpDest`
field, and the callers on the stack keep theirs by the hypothesis.

The old proof is in this file's git history (the merge commit that brought
the lemma in). Do not feel bound by it.

## Domain Constraints

- Never raise or disable the per-step tactic timeout, on the command line or
  in `holproject.toml`. A step over 2.5s is a performance bug in the proof:
  split the step or cut its rewrite set.
- Never wrap a search tactic (`metis_tac`, `meson_tac`, `simp` with a
  search-heavy set, etc.) in `TRY` or `ORELSE`. holbuild's step timeout is
  an exception that `TRY` catches, so such a proof passes locally and hangs
  in CI, which builds with `--skip-proof-steps`. Select goals explicitly
  with `>~`, `>-` and `>|`.
- No `cheat`, `mk_thm`, `new_axiom` or `mk_oracle_thm` in anything you call
  done. Keep the temporary `cheat` only while you are still working.
- Do not change any proved statement in place. Helper lemmas are welcome;
  new hypotheses on existing theorems are not.
- Use `holbuild` only. No Holmake, no `holbuild run` REPL loops unless a
  build cannot answer the question.
- Commit only `spec/prop/vfmJumpDestScript.sml` and this task file. Do not
  commit `.alan/`, `FOCUS_`, `PLAN_`, `STATE_`, `LEARNINGS_`, `LOG_` or tool
  output files; leave them untracked. End every commit message you make with
  exactly these two trailer lines:

```
Co-Authored-By: Claude Code <noreply@anthropic.com>
Bot: deepseek (DeepSeek V4.1 Flash)
```

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| The theorem and its file's helpers | `spec/prop/vfmJumpDestScript.sml` | `all_jumpDest_NONE_def`, `preserves_all_jumpDest_NONE_def` and its family, `preserves_all_jumpDest_NONE_bind`, `..._ignore_bind`, `..._handle`, `..._get_current_context`, `..._set_current_context_jumpDest_NONE`, `same_frame_rel_TL`, and `pop_and_incorporate_context_then_all_jumpDest_NONE` just below this theorem |
| The pop and the state-gas operations | `spec/vfmExecutionScript.sml` | `pop_and_incorporate_context_def` (~line 2122), `pop_context_def`, `unuse_gas_def`, `absorb_state_gas_def`, `credit_new_account_def` (~line 544), `credit_state_gas_refund_def`, `charge_state_gas_def`, `restore_state_gas_def`, `repay_state_gas_spill_def`, `forfeit_remaining_gas_def` |
| Frame and state types | `spec/vfmTypesScript.sml`, `spec/vfmStateScript.sml` | The context and state records, including `jumpDest` and the state-gas fields |
| Property lemmas about the meter | `spec/prop/vfmDecreasesGasScript.sml`, `spec/prop/vfmSameFrameScript.sml`, `spec/prop/vfmStoragePredicatesScript.sml` | Invariants the state-gas operations preserve, including `credit_new_account_contexts` and the `same_frame_rel` family |
| The monadic interface | `spec/vfmExecutionScript.sml`, `spec/prop/vfmExecutionPropScript.sml` | `bind_def`, `ignore_bind_def`, `return_def`, `fail_def`, `assert_def` and the `*_preserves_*` lemmas for them |
| HOL4 | `$HOLDIR` (see `HOLDIR` above) | The toolchain the project pins; its sources are the reference for any library lemma you need |

## Notes

- `pop_and_incorporate_context_then_all_jumpDest_NONE`, immediately below
  this theorem, derives its statement from this one and keeps its own proof;
  it currently builds because this lemma is cheated. Leave it alone, but be
  aware it will have to hold once this one is real.
- `spec/prop/vfmJumpDestScript.sml` is the only place this lemma is used:
  inside this same theory.
- The branch is mid-merge and other theories may be broken; build only
  `vfmJumpDestTheory`. A failure in another theory is not yours to fix.
- If you get stuck, prefer a statement-preserving helper lemma that captures
  the shape the pop actually produces (`all_jumpDest_NONE` only depends on
  the `jumpDest` fields of the context list) over a bigger rewrite set.
