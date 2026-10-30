# TASK: restate and prove the callee-agnostic CALL rules on the state-gas cost model

## Meta
Status: planned
Priority: P1
Created: 2026-10-30
Location: prog/ (the project root is the repository root: holproject.toml)

## Theorem Statement (FROZEN)

This theory's two exported rules are `SPEC_Call_any` and `SPEC_Call_stipend`
(also `caller_observation_frame`, `IMP_EVM_SPEC_FINITE` and
`IMP_EVM_SPEC_FINITE_CODE`).  They are frozen in **content**: the same
callee-agnostic CALL contract they state today, with the state-gas dimension
added exactly as `prog/vfmProgScript.sml` now carries it for the sibling rule
family.

Concretely, the state-gas dimension means:

- `evm_StateGasLeft`, `evm_StateGasSpilled`, `evm_StateGasBaseline` and
  `evm_StateGasCommitted` in the pre and post of a rule that crosses a frame
  boundary, described through the same terms the semantics uses
  (`charge_new_account`, `credit_new_account`, `charge_state_gas`,
  `credit_state_gas_refund`, `absorb_state_gas`,
  `repay_state_gas_spill_context`, `restore_state_gas`,
  `drain_state_gas_reservoir`).
- the CALL's creation charge in the cond as the triplet the sibling rules use:
  `newAccountCharged = (call_inst = Call ∧ 0 < value ∧ account_empty toAccount)`,
  `stateCost = (if newAccountCharged then new_account_state_gas else 0)`,
  `(if newAccountCharged then new_account_state_gas else 0) ≤ sg`, and the cost
  arithmetic written out rather than through an abbreviation;
- the execution-gas cost of the CALL **no longer contains** a
  `new_account_cost` term (`new_account_cost` is gone; the creation charge is
  state gas, taken by `charge_new_account` outside `call_gas`'s cost argument).

**No hypothesis may be added that the state-gas dimension does not force.**
If a rule looks unprovable without one, stop and report it instead of weakening
the rule.  A state-gas hypothesis that the semantics genuinely needs (for
example the reservoir covering `stateCost`) is not a weakening.

The rules as they stand today are in `prog/vfmProgCallScript.sml` at the frozen
commit; read them there rather than from this file.

```
(*
 ************************************************************
 * DO NOT START THESE PROOFS until the machinery they need is
 * built and checked.  This file's rules all go through
 * `call_entry_prepared` and the shared tactics
 * `call_spec_entry_tac` / `call_spec_post_tac` /
 * `call_spec_frame_tac`, so getting those right once is most
 * of the work.
 ************************************************************
 *)
```

## Completion Criteria

1. `holbuild --max-heap 12000 -j8 build vfmProgCallTheory` succeeds from the
   repository root, with no `cheat` anywhere in `prog/vfmProgCallScript.sml`
   and no parser warnings.
2. `SPEC_Call_any`, `SPEC_Call_stipend`, `caller_observation_frame`,
   `IMP_EVM_SPEC_FINITE` and `IMP_EVM_SPEC_FINITE_CODE` keep their names and
   their content apart from the state-gas dimension.  Local lemmas are yours to
   restate, split or merge as the port needs.
3. No `cheat`, no `axiom`, no `mk_thm`, no `TRY`/`ORELSE` around a proof search,
   no change to `tactic_timeout` in `holproject.toml` or on the command line,
   no new hypothesis the state-gas dimension does not force.
4. `git status` clean; no file outside `prog/` touched (the theories below this
   one build unchanged).

**If a rule is false under the state-gas model as stated:**
- Produce a counterexample on concrete values.
- State the tightest sufficient fix and stop there; do not apply it.

## Build

```
cd <the repository root>            # the directory with holproject.toml
holbuild --max-heap 12000 -j8 build vfmProgCallTheory
```

The build resumes from checkpoints by default, which is what you want while
iterating.  Never pass a tactic-timeout override: the project sets
`tactic_timeout = 30` and a step over it is a performance bug (split the step).

## Background

The EVM semantics in `spec/` charge *state gas* as well as execution gas for the
operations that create an account or deposit code (EIP-8037 phase 3).  In
`spec/vfmExecutionScript.sml`:

- `step_call_def` now takes the account-creation charge for a value-bearing
  `CALL` to an empty account before the 63/64 computation, out of the thinned
  `gas_left` (`charge_new_account newAccountCharged`), and gives it back with
  `credit_new_account newAccountCharged` when the child is never entered or
  fails;
- `handle_exception_def`'s failure branch credits the charge (`credit_new_account
  callee.msgParams.newAccountCharged`) over the merged meter before
  `pop_and_incorporate_context`'s absorb/repay;
- `pop_and_incorporate_context_def` absorbs the child's reservoir, spill and
  committed into the parent and, on success, repays the spill through
  `repay_state_gas_spill_context`;
- `proceed_call_def`/`proceed_create_def` drain the parent's reservoir into the
  child's frame; `handle_create_def`'s deposit path charges
  `cost_per_state_byte * LENGTH code` state gas after
  `keccak256_per_word_cost * word_size (LENGTH code)` execution gas.

`prog/vfmProgCallScript.sml` reasons about the same CALL against the pre-state-gas
model, so it names `new_account_cost` (deleted) and its peels follow the old
`step_call_def` spine.  The rules themselves are the callee-agnostic ones: their
point is that the caller observes the callee's effects confined to rollback,
msdomain, originalAccounts, logs, refunds and return data, with no hypothesis
about the callee's code.

## Domain Constraints

- HOL4 + holbuild only.  No Holmake, no `hol4-mcp`, no `--holdir`.
- Never raise or disable the per-step tactic timeout.
- The exported rules' content is frozen (above); statements may not be weakened.
- A theorem proved by one long tactic is one timed unit: give a hard subgoal its
  own lemma.
- The file is public: commit messages say what changed and why in terms of the
  code, and end with exactly:

```
Co-Authored-By: Claude Code <noreply@anthropic.com>
Bot: deepseek (DeepSeek V4.1 Flash)
```

- Never stop another process by name (`pkill -f`, `pkill -x hol`): other builds
  share this machine and this unix user.  Stop your own jobs by PID.
- Do not run the Ethereum execution-spec test suite.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| The ported sibling rules | `prog/vfmProgScript.sml` | `SPEC_Call`, `SPEC_Call_fail_balance`, `SPEC_Call_fail_depth`, `SPEC_Call_precompile`, `step_call_prepared` — already restated on this model and proved; they are the pattern for the charge triplet, the literal cost arithmetic and the state-gas fields |
| The restated semantics | `spec/vfmExecutionScript.sml` | `step_call_def`, `proceed_call_def`, `handle_exception_def`, `handle_step_def`, `handle_create_def`, `charge_new_account_def`, `credit_new_account_def`, `charge_state_gas_def`, `credit_state_gas_refund_def`, `restore_state_gas_def`, `forfeit_remaining_gas_def`, `drain_state_gas_reservoir_def`, `absorb_state_gas_def`, `repay_state_gas_spill_def`, `repay_state_gas_spill_context_def`, `call_gas_def`, `delegate_check_def`, `initial_msg_params_def` |
| The state-gas property layer | `spec/prop/` | `vfmHandleStepTheory`, `vfmAccountFrameTheory`, `vfmRunCallTheory`, `vfmAccountDeletionTheory`, `vfmDecreasesGasTheory`: the frame-boundary laws the rules consume, all restated and green |
| The constants | `spec/vfmConstantsScript.sml` | `new_account_state_gas` 183600, `call_value_cost`, `cost_per_state_byte` 1530, `keccak256_per_word_cost` |
| The rules themselves | `prog/vfmProgCallScript.sml` | `call_entry_prepared` (the spine peel with `once_rewrite_tac[bind_def]` and `access_address_split`), `call_returns_summary`, `call_abort_pair`, `proceed_call_pair`, `handle_exception_memory_return`, the `call_exn_safe_*` family, and the shared entry/post/frame tactics |

## Notes

- `new_account_cost` appears in this file only in `call_entry_prepared`'s
  `call_gas` cost argument and in the two exported rules' conds; everything else
  is structural.
- The rules were proved before the state-gas change, so they are not expected to
  be false; the cost model is what moved.
- The two exported rules have no consumer inside the repository yet — they are
  the callee-agnostic CALL contract for downstream proof work — so keep their
  names and shapes as they are.
