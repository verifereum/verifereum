# TASK: Callee-agnostic CALL rules SPEC_Call_any and SPEC_Call_stipend

## Meta
Status: planned
Priority: P0
Created: 2026-10-28
Location: prog/

## Theorem Statement (FROZEN)

Both theorems are in `prog/vfmProgCallScript.sml` (theory `vfmProgCall`), proved by `cheat` now.

```sml
Theorem SPEC_Call_any:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Memory m * evm_Rollback rb * evm_Msdomain d * evm_ReturnData rd *
   evm_Exception e * evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   evm_OriginalAccounts oa *
   cond (6 + vOff ≤ LENGTH ss ∧
         vOff = (if call_has_value call_inst then 1 else 0) ∧
         ISL e ∧
         gas = w2n (EL 0 ss) ∧ addr = w2w (EL 1 ss) ∧
         value = (if 0 < vOff then w2n (EL 2 ss) else 0) ∧
         argsOffset = w2n (EL (vOff + 2) ss) ∧
         argsSize = w2n (EL (vOff + 3) ss) ∧
         retOffset = w2n (EL (vOff + 4) ss) ∧
         retSize = w2n (EL (vOff + 5) ss) ∧
         max_expansion_range (argsOffset, argsSize) (retOffset, retSize) = (offset, sz) ∧
         em = expanded_memory m offset sz ∧
         toAccount = lookup_account addr rb.accounts ∧
         vCost = (if 0 < value then call_value_cost else 0) ∧
         cCost = (if call_inst = Call ∧ 0 < value ∧ account_empty toAccount
                  then new_account_cost else 0) ∧
         delegate_check toAccount.code
           (msdomain_add addr d) (accesses_add addr rb) dCost newRb newDom ∧
         mCost = memory_cost m offset sz ∧
         call_gas value gas (p.gasLimit - g) mCost
           (access_cost rb addr + vCost + cCost + dCost) = (dynamicGas, calleeGas) ∧
         gasCost = static_gas call_inst + dynamicGas + mCost ∧
         g + gasCost ≤ p.gasLimit ∧
         is_call call_inst ∧ call_inst ≠ Create ∧ call_inst ≠ Create2 ∧
         (0 < value ⇒ ¬p.static) ∧
         ¬fIN addr precompile_addresses ∧
         d = Collect dd))
  {(pc,call_inst)}
  (SEP_EXISTS success out gasLeft calleeLogs calleeAr calleeSr rb' dd' oa'.
   evm_Stack (b2w success :: DROP (6 + vOff) ss) *
   evm_PC (SUC pc) *
   evm_GasUsed (g + gasCost - gasLeft) *
   evm_MsgParams p *
   evm_Memory (buffer_write retOffset (TAKE retSize out) em) *
   evm_Rollback rb' * evm_Msdomain (Collect dd') * evm_ReturnData out *
   evm_Exception (INL ()) *
   evm_AddRefund (ar + if success then calleeAr else 0) *
   evm_SubRefund (sr + if success then calleeSr else 0) *
   evm_Logs (l ++ if success then calleeLogs else []) *
   evm_OriginalAccounts oa' *
   cond (gasLeft ≤ calleeGas ∧ (¬success ⇒ rb' = newRb)))

Theorem SPEC_Call_stipend:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Memory m * evm_Rollback rb * evm_Msdomain d * evm_ReturnData rd *
   evm_Exception e * evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   cond (6 + vOff ≤ LENGTH ss ∧
         vOff = (if call_has_value call_inst then 1 else 0) ∧
         ISL e ∧
         gas = w2n (EL 0 ss) ∧ addr = w2w (EL 1 ss) ∧
         value = (if 0 < vOff then w2n (EL 2 ss) else 0) ∧
         argsOffset = w2n (EL (vOff + 2) ss) ∧
         argsSize = w2n (EL (vOff + 3) ss) ∧
         retOffset = w2n (EL (vOff + 4) ss) ∧
         retSize = w2n (EL (vOff + 5) ss) ∧
         max_expansion_range (argsOffset, argsSize) (retOffset, retSize) = (offset, sz) ∧
         em = expanded_memory m offset sz ∧
         toAccount = lookup_account addr rb.accounts ∧
         vCost = (if 0 < value then call_value_cost else 0) ∧
         cCost = (if call_inst = Call ∧ 0 < value ∧ account_empty toAccount
                  then new_account_cost else 0) ∧
         delegate_check toAccount.code
           (msdomain_add addr d) (accesses_add addr rb) dCost newRb newDom ∧
         mCost = memory_cost m offset sz ∧
         call_gas value gas (p.gasLimit - g) mCost
           (access_cost rb addr + vCost + cCost + dCost) = (dynamicGas, calleeGas) ∧
         gasCost = static_gas call_inst + dynamicGas + mCost ∧
         g + gasCost ≤ p.gasLimit ∧
         is_call call_inst ∧ call_inst ≠ Create ∧ call_inst ≠ Create2 ∧
         (0 < value ⇒ ¬p.static) ∧
         ¬fIN addr precompile_addresses ∧
         d = Collect dd ∧
         calleeGas ≤ call_stipend))
  {(pc,call_inst)}
  (SEP_EXISTS success out gasLeft calleeLogs calleeAr calleeSr rb' dd'.
   evm_Stack (b2w success :: DROP (6 + vOff) ss) *
   evm_PC (SUC pc) *
   evm_GasUsed (g + gasCost - gasLeft) *
   evm_MsgParams p *
   evm_Memory (buffer_write retOffset (TAKE retSize out) em) *
   evm_Rollback rb' * evm_Msdomain (Collect dd') * evm_ReturnData out *
   evm_Exception (INL ()) *
   evm_AddRefund (ar + if success then calleeAr else 0) *
   evm_SubRefund (sr + if success then calleeSr else 0) *
   evm_Logs (l ++ if success then calleeLogs else []) *
   cond (gasLeft ≤ calleeGas ∧
         (if success then
            rb'.accounts =
              (if call_inst ≠ CallCode ∧ 0 < value
               then transfer_value p.callee addr value rb.accounts
               else rb.accounts) ∧
            rb'.toDelete = rb.toDelete
          else rb' = newRb)))
```

**Do not modify these statements.** Prove them as-is, or produce a counterexample.

The definitions they use are in `prog/vfmProgScript.sml` (`SPEC`, `EVM_MODEL`, the `evm_*` predicates, `evm2set_on`, `EVM_SPEC_SEMANTICS`) and `spec/vfmExecutionScript.sml` (`step`, `step_call`, `proceed_call`, `call_gas`, `delegate_check`, `handle_exception`, `pop_and_incorporate_context`, `transfer_value`).

(*
 ************************************************************
 * DO NOT START THIS PROOF until you have finished and
 * validated ALL the machinery you will need for it.
 * Especially machinery that can be generalized and shared
 * between proofs — write it in separate helper theorems
 * and build them first.
 *
 * Building generic, powerful abstractions (lemmas, tactics,
 * conversions, decision procedures) that help this proof
 * IS explicitly in scope — even if they take significant
 * effort. They amortize across the project.
 ************************************************************
 *)

## Completion Criteria

1. `holbuild -j4 build vfmProgCallTheory` from the project root passes with zero CHEAT warnings and zero FAILs, with the project's tactic timeout.
2. No duplicate or near-duplicate lemmas — each helper exists once in its most general form.
3. All new work goes in `prog/vfmProgCallScript.sml` (helpers there may be `[local]` or exported). Don't edit any other `*Script.sml`, `prog/vfmProgScript.sml` and `prog/evmDecompLib.*` above all: other work edits them in parallel. Adding an ancestor theory to `vfmProgCall`'s `Ancestors` is fine.
4. `run_call_reaches_outer_contexts` (already proved in the file) keeps its statement.

**If a theorem is false as stated:**
- Produce a HOL4 counterexample.
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
cd <project root, the directory with holproject.toml>
holbuild -j4 build vfmProgCallTheory
```

## Background

verifereum is an executable EVM semantics in HOL4; `prog/` has a separation-logic program logic over it (`SPEC EVM_MODEL pre code post`). The existing CALL rules (`SPEC_Call`, `SPEC_Call_fail_balance`, `SPEC_Call_fail_depth` in vfmProg) take the CALL step only as far as entering the callee. These two rules take it to the caller's next instruction, whatever code the callee runs, so a contract's caller-side code can be verified without knowing the callee. `SPEC_Call_any` says the callee's effects are confined to the rollback state, the msdomain, originalAccounts, logs, refunds, return data and the return-buffer write. `SPEC_Call_stipend` says that a callee given at most the 2300-gas stipend (as in WETH's `withdraw`) changes no account except by the CALL's own value transfer, which is undone if it fails.

The proof intuition is in a comment above `SPEC_Call_any` in the script.

## Domain Constraints

- holbuild only; no Holmake. Never raise or override the tactic timeout (holproject.toml sets it; don't touch `tactic_timeout` or pass `--tactic-timeout`).
- No `TRY`/`ORELSE` around `metis_tac` or other search tactics.
- No `cheat`, no new axioms, no new hypotheses on the frozen statements.
- Prefer existing definitions; flag any new `Definition` in your final report.
- Don't run the Ethereum test suites (EEST).

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Program logic | `prog/vfmProgScript.sml` | `SPEC`, `evm2set_on`, `EVM_SPEC_SEMANTICS` (line ~307), `IMP_EVM_SPEC_LEMMA` and the local `V_SPEC_CODE` (~583), `rel_sequence_EVM_NEXT_REL_FUNPOW`, `STAR_evm2set`, and the one-step CALL rules `SPEC_Call_fail_balance` (~3917), `SPEC_Call_fail_depth` (~4005), `SPEC_Call` (~4126) |
| Semantics | `spec/vfmExecutionScript.sml` | `step`, `step_call`, `proceed_call`, `call_gas`, `handle_exception`, `pop_and_incorporate_context`, `unuse_gas`, `set_domain`, `dispatch_precompiles` |
| State/contexts | `spec/vfmContextScript.sml`, `spec/vfmStateScript.sml`, `spec/vfmConstantsScript.sml` | records, `call_stipend`, `call_value_cost` |
| wf_state | `spec/prop/vfmExecutionPropScript.sml` | `wf_state`, `gas_stack_ok`, `step_eq_handle_step_inner`, `step_inner` |
| run_call | `spec/prop/vfmRunCallScript.sml` | `run_call`, `run_call_eq_tr`, `step_preserves_wf_state`, `run_call_preserves_wf_state`, `run_call_preserves_txParams`, `step_pop_structure`, `step_push_structure`, `step_call_push_structure` |
| context length | `spec/prop/vfmContextLengthScript.sml` | `run_call_inr_requires_abort_ge2`, `run_call_inl_length`, `step_ge2_inr_is_abort`, `handle_step_not_abort_pops` |
| account frame | `spec/prop/vfmAccountFrameScript.sml` | `run_call_reaches`, `run_call_reaches_inv`, `run_call_reaches_wf_state`, `step_push_foreign`, `step_pop_foreign`, `run_call_static_frame` and its local `step_preserves_static_account_prefix` (template for the stipend invariant) |
| same frame | `spec/prop/vfmRunWithinFrameScript.sml`, `spec/prop/vfmSameFrameScript.sml`, `spec/prop/vfmStaticCallsScript.sml` | `step_same_frame`, `same_frame_rel`, `step_grow_dispatch`, `step_create_reaches_proceed_create`, `step_call_reaches_proceed_call`, `dispatch_precompiles_inr_not_reverted_not_abort` |
| msdomain | `spec/prop/vfmMsdomainPreservedScript.sml`, `spec/prop/vfmDomainSeparationScript.sml` | how msdomain evolves; Collect vs Enforce |
| gas | `spec/prop/vfmDecreasesGasScript.sml`, `spec/prop/vfmHeadGasScript.sml` | gas monotonicity |
| SSTORE sentry | `spec/vfmExecutionScript.sml`, `step_sstore_gas_consumption` | `call_stipend < gasLeft` check |
| Existing helper | `prog/vfmProgCallScript.sml` | `run_call_reaches_outer_contexts` (proved) |

## Notes

- The project's tactic timeout is 30 s per step (holproject.toml).
- The HOL toolchain and all ancestors are already built in this worktree; only vfmProgCallTheory rebuilds.
