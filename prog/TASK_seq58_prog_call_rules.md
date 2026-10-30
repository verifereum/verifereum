# TASK: repair the state-gas (EIP-8037) restatement of the CALL rules in prog/vfmProgScript.sml

## Meta
Status: planned
Priority: P1
Created: 2026-10-30
Location: prog/ (the project root is the repository root: holproject.toml)

## Theorem Statement (FROZEN)

The primary obligation. Prove it as-is, or produce a counterexample.

```sml
Theorem SPEC_Call_fail_balance:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_StateGasLeft sg * evm_StateGasSpilled sp *
   evm_Memory m * evm_Rollback rb * evm_Msdomain d * evm_ReturnData rd *
   evm_Exception e *
   cond (7 ≤ LENGTH ss ∧ ISL e ∧
         gas = w2n (EL 0 ss) ∧ addr = w2w (EL 1 ss) ∧ value = w2n (EL 2 ss) ∧
         argsOffset = w2n (EL 3 ss) ∧ argsSize = w2n (EL 4 ss) ∧
         retOffset = w2n (EL 5 ss) ∧ retSize = w2n (EL 6 ss) ∧
         max_expansion_range (argsOffset, argsSize) (retOffset, retSize) = (offset, sz) ∧
         em = expanded_memory m offset sz ∧
         access_check d addr ∧
         toAccount = lookup_account addr rb.accounts ∧
         vCost = (if 0 < value then call_value_cost else 0) ∧
         newAccountCharged = (call_inst = Call ∧ 0 < value ∧
                              account_empty toAccount) ∧
         stateCost = (if newAccountCharged then new_account_state_gas else 0) ∧
         (if newAccountCharged then new_account_state_gas else 0) ≤ sg ∧
         creditBack = MIN stateCost sp ∧
         delegate_check toAccount.code
           (msdomain_add addr d) (accesses_add addr rb) dCost newRb newDom ∧
         mCost = memory_cost m offset sz ∧
         call_gas value gas
           (p.gasLimit - (g + (static_gas call_inst +
              access_cost rb addr + vCost + dCost + mCost))) 0 0 =
             (dynamicGas, stipend) ∧
         g + (static_gas call_inst + access_cost rb addr + vCost + dCost + mCost) ≤
           p.gasLimit ∧
         g + (static_gas call_inst + access_cost rb addr + vCost + dCost + mCost +
              dynamicGas) ≤ p.gasLimit ∧
         stipend ≤ g + (static_gas call_inst + access_cost rb addr + vCost + dCost +
                       mCost + dynamicGas) - creditBack ∧
         ¬p.static ∧
         call_has_value call_inst ∧
         sender = lookup_account p.callee rb.accounts ∧
         sender.balance < value))
  {(pc,call_inst)}
  (evm_Stack (b2w F :: DROP 7 ss) *
   evm_PC (SUC pc) *
   evm_GasUsed (g + (static_gas call_inst + access_cost rb addr + vCost + dCost +
                     mCost + dynamicGas) - creditBack - stipend) *
   evm_StateGasLeft (sg - creditBack) *
   evm_StateGasSpilled (sp - creditBack) *
   evm_MsgParams p *
   evm_Memory em *
   evm_Rollback newRb *
   evm_Msdomain newDom *
   evm_Exception (INL ()) *
   evm_ReturnData [])
```

This statement is one of a family that the state-gas restatement (EIP-8037
phase 3: the account-creation charge, the code-deposit charge) has broken.  The
other statements of the same family are frozen too, and their proofs are also
failing:

| Theorem | Line (when this file was written) |
|---------|-----------------------------------|
| `SPEC_Call_fail_depth` | 4926 |
| `SPEC_Call` | 5056 |
| `step_call_prepared` | 5283 |
| `SPEC_Call_precompile` | 5726 |

Their statements were restated deliberately (they carry `stateCost`,
`creditBack`, `newAccountCharged` and `evm_StateGasLeft`/`evm_StateGasSpilled`);
reproduce them exactly as they stand.

**Do not modify these statements.**  Prove them as-is, or produce a
counterexample.  If one of them is false as written, say which premise fails
and stop for that theorem, rather than weakening it.

```
(*
 ************************************************************
 * DO NOT START THESE PROOFS until you have finished and
 * validated ALL the machinery you will need.  The rules in
 * this file share a big rewrite/tactic vocabulary
 * (`end_tac`, `exn_inner_tac`, `binop_tac`, `IMP_EVM_SPEC`),
 * and several of the failures are the same structural problem
 * in different rules: a normalisation lemma or a peeled spine
 * that the whole family can use is worth building first.
 ************************************************************
 *)
```

## Completion Criteria

1. `holbuild --max-heap 12000 -j8 build vfmProgTheory` succeeds from the
   repository root, with no `cheat` left anywhere in `prog/vfmProgScript.sml`
   and no parser warnings.
2. No statement change: every `Theorem` name that exists at the frozen commit
   still exists, and each one states the same thing (byte-identical up to the
   whitespace of the frozen statements above).
3. No new hypothesis, no `cheat`, no `axiom`, no `mk_thm`, no `TRY` or `ORELSE`
   around `metis_tac` or another proof search, no `tactic_timeout` change.
   New helper lemmas are welcome, marked `[local]` if nothing else uses them.
4. `git status` clean; no file outside `prog/` touched.

**If a theorem is false as stated:**
- Produce a counterexample on concrete values (`EVAL_TAC`/`cv_eval` style).
- State the tightest sufficient fix and stop there; do not apply it.

## Build

```
cd <the repository root>            # the directory with holproject.toml
holbuild --max-heap 12000 -j8 build vfmProgTheory
```

The build resumes from checkpoints by default, which is what you want while
iterating.  Do not pass `--tactic-timeout`: the project sets `tactic_timeout`
in `holproject.toml` and it must not be raised.

## Background

The EVM semantics in `spec/` have been restated to charge *state gas* as well
as execution gas for the operations that create an account or deposit code
(EIP-8037): a CALL with value to a non-existent account charges
`new_account_state_gas` (183600) before the child frame is entered, out of the
state-gas reservoir, and refunds it when the child fails or the frame is never
entered; CREATE/CREATE2 charge the destination's creation before the 63/64
withholding; the code deposit charges `cost_per_state_byte * LENGTH code` state
gas with `keccak256_per_word_cost * word_size (LENGTH code)` execution gas
first, inside the path that restores and forfeits; SELFDESTRUCT's sweep charges
183600 state gas and `self_destruct_new_account_cost` (9000) execution gas.

`prog/` reasons about the same steps with `SPEC` rules.  The rules here were
written for the execution-gas-only model and have been restated by hand; their
proofs are what is broken.  Everything below this file in the dependency graph
builds.

The ordering the restatement must respect (it is the ordering the semantics
implements, and the one the Ethereum execution-spec tests can see):
execution gas before state gas; a CALL's creation charge before the 63/64
computation and out of the thinned `gas_left`; a CREATE's before the
withholding and decided independently of the collision check; the deposit's
hash cost in execution gas before its byte cost in state gas, inside the
failure path; the child-never-entered path returns the drained reservoir as
well as the withheld execution gas.

## Domain Constraints

- HOL4 + holbuild only.  No Holmake, no `hol4-mcp`, no `--holdir`, no
  `--no-cache` for the build you report.
- Never raise or disable the per-step tactic timeout: a step that runs over is
  a performance bug in the proof (split it, cut its rewrite set).
- Statements are frozen (see above).  Weakening a hypothesis or adding one is a
  change to the statement.
- A theorem proved by a single long tactic is one timed unit; give a hard
  subgoal its own lemma rather than one giant `gvs`.
- The file is public: commit messages say what changed and why, in terms of the
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
| The restated semantics | `spec/vfmExecutionScript.sml` | `step_call_def`, `step_create_def`, `step_self_destruct_def`, `handle_create_def`, `handle_exception_def`, `handle_step_def`, `charge_new_account_def`, `credit_new_account_def`, `charge_state_gas_def`, `credit_state_gas_refund_def`, `restore_state_gas_def`, `forfeit_remaining_gas_def`, `call_gas_def`, `delegate_check_def` |
| The state-gas constants | `spec/vfmConstantsScript.sml` | `new_account_state_gas` 183600, `cost_per_state_byte` 1530, `keccak256_per_word_cost`, `self_destruct_new_account_cost` 9000, `call_value_cost` |
| The rules to repair | `prog/vfmProgScript.sml` | the CALL/CREATE/SELFDESTRUCT `SPEC` rules and their shared tactic vocabulary (`IMP_EVM_SPEC`, `end_tac`, `exn_inner_tac`, `binop_tac`) |
| Callee-agnostic CALL machinery | `prog/vfmProgCallScript.sml` | written against the pre-state-gas cost model and so not part of this build, but `call_entry_prepared` (about line 2317) peels the same `step_call` spine step by step with `once_rewrite_tac[bind_def]` and `access_address_split`, which is a working pattern for the same program shape |
| The property layer | `spec/prop/` | `vfmExecutionPropTheory`, `vfmHandleStepTheory`, `vfmAccountFrameTheory`, `vfmRunCallTheory`, `vfmDecreasesGasTheory` and the rest: all restated to the same model and all green |
| CREATE-rule precedent | `prog/vfmProgScript.sml` | `SPEC_Create_fail_created` and `SPEC_Create_original` are the same restatement already proved for the create family; their per-goal dispatcher is the model for the call rules' |
| A previous attempt | `prog/vfmProgScript.sml`, just above the `cheat`, and in the branch history at commit `18ae66bf` | reaches 12 residual goals and says why they do not close |

## Notes

- The statements were proved before the restatement (`git log -S` on the
  theorem names, or the branch's merge base with the upstream default branch),
  so they are not expected to be false; the failure is in the proofs.
- The residual goals in the previous attempt are all in the branches where the
  charged step fails: an `access_address` is case-split instead of reduced
  because `access_address_split`'s side condition is stated through an
  abbreviation variable.
