Theory vfmSettlement
Ancestors vfmCompute
Libs cv_transLib wordsLib

(* Small transaction fixtures, independent of the external conformance suite. *)
Definition settlement_block_def:
  settlement_block coinbase = <|
    baseFeePerGas := 1; excessBlobGas := 0; gasUsed := 0; blobGasUsed := 0;
    number := 1; timeStamp := 1; coinBase := coinbase; gasLimit := 1000000;
    prevRandao := 0w; hash := 0w; rlpSize := 0;
    parentBeaconBlockRoot := 0w; requestsHash := 0w; blockAccessListHash := 0w;
    slotNumber := 0; stateRoot := 0w;
    withdrawalsRoot := 0w; transactions := []; withdrawals := [] |>
End
val () = cv_auto_trans settlement_block_def;

Definition settlement_tx_def:
  settlement_tx = <|
    from := 0x100w; to := SOME 0x200w; data := []; nonce := 0; value := 0;
    gasLimit := 21000; gasPrice := 2; accessList := [];
    blobVersionedHashes := []; maxFeePerBlobGas := NONE;
    maxFeePerGas := NONE; authorizationList := [] |>
End
val () = cv_auto_trans settlement_tx_def;

Definition settlement_accounts_def:
  settlement_accounts balance = update_account 0x100w
    (empty_account_state with balance := balance) empty_accounts
End
val () = cv_auto_trans settlement_accounts_def;

(* Keep rejection distinguishable from execution success and inspect both payees. *)
Definition settlement_observation_def:
  settlement_observation coinbase accounts tx =
    OPTION_MAP (λ(tr, acc).
      (tr.result, tr.gasUsed,
       (lookup_account tx.from acc).balance,
       (lookup_account tx.from acc).nonce,
       (lookup_account coinbase acc).balance,
       account_empty (lookup_account coinbase acc)))
    (run_transaction (Collect empty_domain) F 1 []
      (settlement_block coinbase) accounts tx)
End
val () = cv_auto_trans settlement_observation_def;

Theorem settlement_sender_is_coinbase:
  settlement_observation 0x100w (settlement_accounts 100000) settlement_tx =
    SOME (NONE, 21000, 79000, 1, 79000, F)
Proof
  CONV_TAC cv_eval
QED

Theorem settlement_distinct_coinbase:
  settlement_observation 0x300w (settlement_accounts 100000) settlement_tx =
    SOME (NONE, 21000, 58000, 1, 21000, F)
Proof
  CONV_TAC cv_eval
QED

Theorem settlement_unused_gas_and_tip:
  settlement_observation 0x100w (settlement_accounts 100000)
    (settlement_tx with gasLimit := 40000) =
    SOME (NONE, 21000, 79000, 1, 79000, F)
Proof
  CONV_TAC cv_eval
QED

Theorem settlement_zero_tip_empty_coinbase:
  settlement_observation 0x300w (settlement_accounts 100000)
    (settlement_tx with gasPrice := 1) =
    SOME (NONE, 21000, 79000, 1, 0, T)
Proof
  CONV_TAC cv_eval
QED

Theorem settlement_created_coinbase_selfdestruct:
  settlement_observation (address_for_create 0x100w 0)
    (settlement_accounts 1000000)
    (settlement_tx with <| to := NONE; data := [0x30w; 0xffw];
                          gasLimit := 100000 |>) =
    SOME (NONE, 38036, 923928, 1, 0, T)
Proof
  CONV_TAC cv_eval
QED

Theorem settlement_created_coinbase_selfdestruct_zero_tip:
  settlement_observation (address_for_create 0x100w 0)
    (settlement_accounts 1000000)
    (settlement_tx with <| to := NONE; data := [0x30w; 0xffw];
                          gasLimit := 100000; gasPrice := 1 |>) =
    SOME (NONE, 38036, 961964, 1, 0, T)
Proof
  CONV_TAC cv_eval
QED

Theorem settlement_reverted_sender_is_coinbase:
  settlement_observation 0x100w
    (update_account 0x200w
      (empty_account_state with code := [0x60w; 0w; 0x60w; 0w; 0xfdw])
      (settlement_accounts 100000))
    (settlement_tx with gasLimit := 40000) =
    SOME (SOME Reverted, 21006, 78994, 1, 78994, F)
Proof
  CONV_TAC cv_eval
QED

Theorem settlement_storage_refund_and_tip:
  settlement_observation 0x100w
    (update_account 0x200w
      (empty_account_state with <|
        code := [0x60w; 0w; 0x60w; 0w; 0x55w; 0w];
        storage := update_storage 0w 1w empty_storage |>)
      (settlement_accounts 1000000))
    (settlement_tx with gasLimit := 100000) =
    SOME (NONE, 21206, 978794, 1, 978794, F)
Proof
  CONV_TAC cv_eval
QED
