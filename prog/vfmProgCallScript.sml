(* CALL to arbitrary code, as one SPEC step for the caller: control comes
   back to the caller's frame with the callee's effects confined to the
   rollback state, logs and refunds. *)
Theory vfmProgCall
Ancestors
  vfmProg vfmExecution vfmExecutionProp vfmContext vfmConstants vfmState
  vfmDecreasesGas vfmRunCall vfmContextLength vfmAccountFrame
  vfmTypes vfmBuffer
  prog set_sep pred_set pair list arithmetic option finite_map combin

(* The precondition is SPEC_Call's without the balance and depth checks:
   when those fail the CALL returns 0 at once, which the postcondition
   covers. The caller owns every Parsed element, since the callee's frames
   run arbitrary code at arbitrary pcs. *)
Theorem SPEC_Call_any:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Memory m * evm_Rollback rb * evm_Msdomain d * evm_ReturnData rd *
   evm_JumpDest j * evm_Exception e * evm_CachedRB cb * evm_Contexts cs *
   evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   evm_OriginalAccounts oa *
   evm_Parsed pc call_inst * evm_hide_Parsed (UNIV DELETE pc) *
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
         access_check d addr ∧
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
         ¬fIN addr precompile_addresses))
  {}
  (SEP_DISJ
    (SEP_EXISTS success out gasLeft calleeLogs calleeAr calleeSr rb' d' oa'.
     evm_Stack (b2w success :: DROP (6 + vOff) ss) *
     evm_PC (SUC pc) *
     evm_GasUsed (g + gasCost - gasLeft) *
     evm_MsgParams p *
     evm_Memory (buffer_write retOffset (TAKE retSize out) em) *
     evm_Rollback rb' * evm_Msdomain d' * evm_ReturnData out *
     evm_JumpDest j * evm_Exception (INL ()) * evm_CachedRB cb *
     evm_Contexts cs *
     evm_AddRefund (ar + if success then calleeAr else 0) *
     evm_SubRefund (sr + if success then calleeSr else 0) *
     evm_Logs (l ++ if success then calleeLogs else []) *
     evm_OriginalAccounts oa' *
     evm_Parsed pc call_inst * evm_hide_Parsed (UNIV DELETE pc) *
     cond (gasLeft ≤ calleeGas ∧ (¬success ⇒ rb' = newRb)))
    (SEP_EXISTS x. evm_Exception (INR x) * cond (vfm_abort x) * SEP_T))
Proof
  cheat
QED

(* With at most the 2300-gas stipend, no frame of the callee can SSTORE
   (EIP-2200 sentry), CALL with value (9000), SELFDESTRUCT (5000) or CREATE
   (32000), so no account changes apart from the CALL's own value transfer,
   which is undone if the callee fails. *)
Theorem SPEC_Call_stipend:
  SPEC EVM_MODEL
  (evm_Stack ss * evm_PC pc * evm_GasUsed g * evm_MsgParams p *
   evm_Memory m * evm_Rollback rb * evm_Msdomain d * evm_ReturnData rd *
   evm_JumpDest j * evm_Exception e * evm_CachedRB cb * evm_Contexts cs *
   evm_AddRefund ar * evm_SubRefund sr * evm_Logs l *
   evm_OriginalAccounts oa *
   evm_Parsed pc call_inst * evm_hide_Parsed (UNIV DELETE pc) *
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
         access_check d addr ∧
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
         calleeGas ≤ call_stipend))
  {}
  (SEP_DISJ
    (SEP_EXISTS success out gasLeft calleeLogs calleeAr calleeSr rb' d'.
     evm_Stack (b2w success :: DROP (6 + vOff) ss) *
     evm_PC (SUC pc) *
     evm_GasUsed (g + gasCost - gasLeft) *
     evm_MsgParams p *
     evm_Memory (buffer_write retOffset (TAKE retSize out) em) *
     evm_Rollback rb' * evm_Msdomain d' * evm_ReturnData out *
     evm_JumpDest j * evm_Exception (INL ()) * evm_CachedRB cb *
     evm_Contexts cs *
     evm_AddRefund (ar + if success then calleeAr else 0) *
     evm_SubRefund (sr + if success then calleeSr else 0) *
     evm_Logs (l ++ if success then calleeLogs else []) *
     evm_OriginalAccounts oa *
     evm_Parsed pc call_inst * evm_hide_Parsed (UNIV DELETE pc) *
     cond (gasLeft ≤ calleeGas ∧
           (if success then
              rb'.accounts =
                (if call_inst ≠ CallCode ∧ 0 < value
                 then transfer_value p.callee addr value rb.accounts
                 else rb.accounts) ∧
              rb'.toDelete = rb.toDelete
            else rb' = newRb)))
    (SEP_EXISTS x. evm_Exception (INR x) * cond (vfm_abort x) * SEP_T))
Proof
  cheat
QED
