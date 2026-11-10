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
    SOME (NONE, 15000, 85000, 1, 85000, F)
Proof
  CONV_TAC cv_eval
QED

Theorem settlement_distinct_coinbase:
  settlement_observation 0x300w (settlement_accounts 100000) settlement_tx =
    SOME (NONE, 15000, 70000, 1, 15000, F)
Proof
  CONV_TAC cv_eval
QED

Theorem settlement_unused_gas_and_tip:
  settlement_observation 0x100w (settlement_accounts 100000)
    (settlement_tx with gasLimit := 40000) =
    SOME (NONE, 15000, 85000, 1, 85000, F)
Proof
  CONV_TAC cv_eval
QED

Theorem settlement_zero_tip_empty_coinbase:
  settlement_observation 0x300w (settlement_accounts 100000)
    (settlement_tx with gasPrice := 1) =
    SOME (NONE, 15000, 85000, 1, 0, T)
Proof
  CONV_TAC cv_eval
QED

(* EIP-8037 phase 3: a create transaction charges its new account 183600
   state gas at the top frame, out of the reservoir first and then out of
   the execution grant.  A 100000-gas create has neither: the limit is
   below EIP-7825's 2**24 cap, so the reservoir is empty, and the grant is
   75966.  The transaction halts at entry with OutOfGas and forfeits the
   frame's whole grant; the sender still pays the fee, its nonce is still
   taken, and the coinbase is credited. *)
Theorem settlement_created_coinbase_selfdestruct:
  settlement_observation (address_for_create 0x100w 0)
    (settlement_accounts 1000000)
    (settlement_tx with <| to := NONE; data := [0x30w; 0xffw];
                          gasLimit := 100000 |>) =
    SOME (SOME OutOfGas, 100000, 800000, 1, 100000, F)
Proof
  CONV_TAC cv_eval
QED

Theorem settlement_created_coinbase_selfdestruct_zero_tip:
  settlement_observation (address_for_create 0x100w 0)
    (settlement_accounts 1000000)
    (settlement_tx with <| to := NONE; data := [0x30w; 0xffw];
                          gasLimit := 100000; gasPrice := 1 |>) =
    SOME (SOME OutOfGas, 100000, 900000, 1, 0, T)
Proof
  CONV_TAC cv_eval
QED

(* The same creation, funded: EIP-8037's state gas comes out of the part of
   the gas limit above EIP-7825's 2**24 cap, so a 20000000-gas transaction
   funds the 183600 the destination's creation needs out of its reservoir
   and the create runs.  The contract self-destructs to itself, which is the
   coinbase, and keeps its (zero) balance when it is cleared, so the only
   thing in the coinbase is the transaction's tip. *)
Theorem settlement_created_coinbase_selfdestruct_funded:
  settlement_observation (address_for_create 0x100w 0)
    (settlement_accounts 100000000)
    (settlement_tx with <| to := NONE; data := [0x30w; 0xffw];
                          gasLimit := 20000000 |>) =
    SOME (NONE, 212636, 99574728, 1, 212636, F)
Proof
  CONV_TAC cv_eval
QED

Theorem settlement_reverted_sender_is_coinbase:
  settlement_observation 0x100w
    (update_account 0x200w
      (empty_account_state with code := [0x60w; 0w; 0x60w; 0w; 0xfdw])
      (settlement_accounts 100000))
    (settlement_tx with gasLimit := 40000) =
    SOME (SOME Reverted, 15006, 84994, 1, 84994, F)
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
    SOME (NONE, 21685, 978315, 1, 978315, F)
Proof
  CONV_TAC cv_eval
QED
