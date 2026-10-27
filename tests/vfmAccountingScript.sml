Theory vfmAccounting
Ancestors vfmCompute vfmExecution
Libs cv_transLib wordsLib

(* These reference equations freeze the inline calculations and effect order
   before extraction. Equality is checked for all inputs, including failures. *)
Definition sstore_gas_consumption_inline_def:
  sstore_gas_consumption_inline address key value = do
    gasLeft <- get_gas_left;
    assert (call_stipend < gasLeft) OutOfGas;
    accounts <- get_accounts;
    currentValue <<- lookup_storage key (lookup_account address accounts).storage;
    original <- get_original;
    originalValue <<- lookup_storage key (lookup_account address original).storage;
    accessCost <- access_slot (SK address key);
    baseDynamicGas <<-
      if originalValue = currentValue ∧ currentValue ≠ value
      then if originalValue = 0w
           then storage_set_cost
           else storage_update_cost - cold_sload_cost
      else warm_access_cost;
    dynamicGas <<- baseDynamicGas + zero_warm accessCost;
    refundUpdates <<-
      if currentValue ≠ value then
        let storageSetRefund =
          if originalValue = value then
            if originalValue = 0w then
              storage_set_cost - warm_access_cost
            else
              storage_update_cost - cold_sload_cost - warm_access_cost
          else 0
        in
          if originalValue ≠ 0w ∧ currentValue ≠ 0w ∧ value = 0w then
            (storageSetRefund + storage_clear_refund, 0)
          else if originalValue ≠ 0w ∧ currentValue = 0w then
            (storageSetRefund, storage_clear_refund)
          else (storageSetRefund, 0)
      else (0, 0);
    update_gas_refund refundUpdates;
    consume_gas dynamicGas;
  od
End

Definition transaction_accounting_inline_def:
  transaction_accounting_inline blk tx result acc t =
  let (gasLimit, gasUsed, stateGasLeft, addRefund, subRefund, logs, returnData) =
    if NULL t.contexts ∨ ¬NULL (TL t.contexts)
    then (0, 0, 0, 0, 0, [], MAP (n2w o ORD) "not exactly one remaining context")
    else let ctxt = FST $ HD t.contexts in
      (ctxt.msgParams.gasLimit, ctxt.gasUsed, ctxt.stateGasLeft,
       ctxt.addRefund, ctxt.subRefund, ctxt.logs, ctxt.returnData) in
  let gasLeft = gasLimit - gasUsed in
  let txGasUsed = tx.gasLimit - gasLeft - stateGasLeft in
  let storageRefund = if result ≠ NONE then 0 else addRefund - subRefund in
  let gasRefund = MIN (txGasUsed DIV 5) (t.txParams.authRefund + storageRefund) in
  let floor_cost = calldata_floor_cost tx.accessList (IS_NONE tx.to)
                                    (tx.to = SOME tx.from) tx.value tx.data in
  let totalGasUsed = MAX (txGasUsed - gasRefund) floor_cost in
  let stateGasUsed = (t.txParams.stateGasReservoir - stateGasLeft) +
                     t.txParams.stateGasSpilled + t.txParams.stateGasCommitted in
  let executionGasUsed = MAX (txGasUsed - stateGasUsed) floor_cost in
  let refundEther = (tx.gasLimit - totalGasUsed) * tx.gasPrice in
  let priorityFeePerGas = tx.gasPrice - blk.baseFeePerGas in
  let transactionFee = totalGasUsed * priorityFeePerGas in
  let accounts = if result = NONE then t.rollback.accounts else acc in
  let sender = lookup_account tx.from accounts in
  let accounts = update_account tx.from
    (sender with balance updated_by $+ refundEther) accounts in
  let feeRecipient = lookup_account blk.coinBase accounts in
  let accounts = update_account blk.coinBase
    (feeRecipient with balance updated_by $+ transactionFee) accounts in
  let newAccounts = if result = NONE
                    then process_deletions t.rollback.toDelete accounts
                    else accounts in
  let logs = if result = NONE then logs else [] in
  let tr = <| gasUsed := totalGasUsed;
              executionGasUsed := executionGasUsed;
              stateGasUsed := stateGasUsed;
              logs := logs;
              result := result;
              output := returnData;
              domain := t.msdomain |> in
  (tr, newAccounts)
End

Theorem sstore_gas_consumption_equiv:
  step_sstore_gas_consumption = sstore_gas_consumption_inline
Proof
  simp[FUN_EQ_THM, step_sstore_gas_consumption_def,
       sstore_gas_consumption_inline_def, sstore_base_gas_def,
       sstore_refund_updates_def]
QED

Theorem transaction_accounting_equiv:
  post_transaction_accounting = transaction_accounting_inline
Proof
  SIMP_TAC pure_ss [FUN_EQ_THM] >>
  map_every qx_gen_tac [`blk`, `tx`, `result`, `acc`, `t`] >>
  Cases_on `NULL t.contexts \/ ~NULL (TL t.contexts)` >>
  ASM_SIMP_TAC pure_ss [post_transaction_accounting_def,
    transaction_accounting_inline_def, transaction_gas_accounting_def,
    LET_THM, COND_CLAUSES, pairTheory.pair_case_thm,
    pairTheory.UNCURRY_DEF] >>
  REFL_TAC
QED

(* Clean/dirty slots, clearing, undoing a clear and restoring original values. *)
Theorem sstore_cost_cases:
  sstore_base_gas 0w 0w 0w = 100 ∧
  sstore_base_gas 0w 0w 1w = 20000 ∧
  sstore_base_gas 1w 1w 0w = 2900 ∧
  sstore_base_gas 1w 1w 2w = 2900 ∧
  sstore_base_gas 1w 0w 1w = 100 ∧
  sstore_base_gas 0w 1w 0w = 100 ∧
  sstore_base_gas 1w 2w 1w = 100 ∧
  sstore_base_gas 1w 2w 0w = 100
Proof
  CONV_TAC cv_eval
QED

Theorem sstore_refund_cases:
  sstore_refund_updates 1w 1w 1w = (0,0) ∧
  sstore_refund_updates 0w 0w 1w = (0,0) ∧
  sstore_refund_updates 1w 1w 0w = (4800,0) ∧
  sstore_refund_updates 1w 0w 1w = (2800,4800) ∧
  sstore_refund_updates 1w 0w 2w = (0,4800) ∧
  sstore_refund_updates 0w 1w 0w = (19900,0) ∧
  sstore_refund_updates 1w 2w 1w = (2800,0) ∧
  sstore_refund_updates 1w 2w 0w = (4800,0)
Proof
  CONV_TAC cv_eval
QED

(* The block's two dimensions ignore the refund, the receipt's does not,
   and the state dimension comes off the execution one: a transaction
   with no state gas is unchanged, one that draws its reservoir reports
   the draw as state gas and the rest as execution, and a spill with a
   committed part counts in the state dimension even though the gas left
   the execution budget. *)
Theorem transaction_gas_accounting_cases:
  transaction_gas_accounting 2 1 100000 0 0 0 21000 (60000,0,10000,0) =
    (32000,40000,0,136000,32000) ∧
  transaction_gas_accounting 2 1 100000 0 0 0 35000 (60000,0,10000,0) =
    (35000,40000,0,130000,35000) ∧
  transaction_gas_accounting 2 1 220000 100000 0 0 21000 (60000,40000,0,0) =
    (120000,60000,60000,200000,120000) ∧
  transaction_gas_accounting 1 1 100000 1000 2000 500 0 (90000,0,0,0) =
    (10000,6500,3500,90000,0)
Proof
  CONV_TAC cv_eval
QED
