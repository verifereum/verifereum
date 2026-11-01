Theory vfmCreateCollision
Ancestors vfmCompute vfmSettlement
Libs cv_transLib wordsLib

(* Creation into an address with nonce 0 and no code succeeds even when the
   address has storage, and the storage is cleared. *)

Definition collision_storage_def:
  collision_storage = update_storage 0w 1w empty_storage
End
val () = cv_auto_trans collision_storage_def;

Definition collision_observation_def:
  collision_observation target accounts tx =
    OPTION_MAP (λ(tr, acc).
      (tr.result, tr.gasUsed,
       (lookup_account target acc).nonce,
       lookup_storage 0w (lookup_account target acc).storage))
    (run_transaction (Collect empty_domain) F 1 []
      (settlement_block 0x300w) accounts tx)
End
val () = cv_auto_trans collision_observation_def;

(* A creation transaction with empty initcode. *)
Definition collision_tx_accounts_def:
  collision_tx_accounts =
    update_account (address_for_create 0x100w 0)
      (empty_account_state with storage := collision_storage)
      (settlement_accounts 1000000)
End
val () = cv_auto_trans collision_tx_accounts_def;

Theorem create_tx_storage_only_target:
  collision_observation (address_for_create 0x100w 0) collision_tx_accounts
    (settlement_tx with <| to := NONE; gasLimit := 153000 |>) =
    SOME (NONE, 53000, 1, 0w)
Proof
  CONV_TAC cv_eval
QED

(* The CREATE opcode with empty initcode: PUSH0 PUSH0 PUSH0 CREATE STOP. *)
Definition collision_op_accounts_def:
  collision_op_accounts =
    update_account (address_for_create 0x200w 1)
      (empty_account_state with storage := collision_storage)
      (update_account 0x200w
        (empty_account_state with <|
           nonce := 1; code := [0x5fw; 0x5fw; 0x5fw; 0xf0w; 0w] |>)
        (settlement_accounts 1000000))
End
val () = cv_auto_trans collision_op_accounts_def;

(* The observation without the gas used. *)
Definition collision_outcome_def:
  collision_outcome target accounts tx =
    OPTION_MAP (λ(r, g, n, v). (r, n, v))
      (collision_observation target accounts tx)
End
val () = cv_auto_trans collision_outcome_def;

Theorem create_op_storage_only_target:
  collision_outcome (address_for_create 0x200w 1) collision_op_accounts
    (settlement_tx with gasLimit := 200000) =
    SOME (NONE, 1, 0w)
Proof
  CONV_TAC cv_eval
QED

(* A creation transaction whose initcode reverts (PUSH0 PUSH0 REVERT): the
   creation is rolled back, so the target keeps nonce 0 and its storage. *)
Theorem create_tx_storage_only_target_revert:
  collision_outcome (address_for_create 0x100w 0) collision_tx_accounts
    (settlement_tx with <| to := NONE; gasLimit := 153000;
                           data := [0x5fw; 0x5fw; 0xfdw] |>) =
    SOME (SOME Reverted, 0, 1w)
Proof
  CONV_TAC cv_eval
QED
