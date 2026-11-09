Theory vfmSystemTransaction
Ancestors vfmCompute vfmSettlement
Libs cv_transLib wordsLib

(* Small modified contracts, independent of the external conformance suite. *)
Definition system_test_accounts_def:
  system_test_accounts code =
    update_account withdrawal_request_contract
      (empty_account_state with <| code := code; nonce := 1; balance := 23;
        storage := update_storage 0w 5w empty_storage |>)
    (update_account system_address
      (empty_account_state with <| nonce := 9; balance := 17 |>)
    (update_account 0x300w
      (empty_account_state with <| nonce := 1; balance := 19 |>) empty_accounts))
End
val () = cv_auto_trans system_test_accounts_def;

Definition system_test_call_def:
  system_test_call checked code =
    run_system_transaction checked (Collect empty_domain) 1 []
      (settlement_block 0x300w) (system_test_accounts code)
      withdrawal_request_contract (word_to_bytes (42w:bytes32) T)
End
val () = cv_auto_trans system_test_call_def;

Definition system_test_observation_def:
  system_test_observation checked code =
    OPTION_MAP (λ(output, accounts, dom).
      (output, lookup_storage 0w (lookup_account withdrawal_request_contract accounts).storage,
       (lookup_account system_address accounts).balance,
       (lookup_account system_address accounts).nonce,
       (lookup_account withdrawal_request_contract accounts).balance,
       (lookup_account withdrawal_request_contract accounts).nonce,
       (lookup_account 0x300w accounts).balance))
    (system_test_call checked code)
End
val () = cv_auto_trans system_test_observation_def;

Theorem system_modified_return_bytes:
  system_test_observation T
    [0x60w; 0xaaw; 0x5fw; 0x53w; 0x60w; 1w; 0x5fw; 0xf3w] =
  SOME ([0xaaw], 5w, 17, 9, 23, 1, 19)
Proof
  CONV_TAC cv_eval
QED

Theorem system_success_keeps_storage_without_fees:
  system_test_observation T [0x60w; 7w; 0x5fw; 0x55w; 0w] =
  SOME ([], 7w, 17, 9, 23, 1, 19)
Proof
  CONV_TAC cv_eval
QED

Theorem system_empty_code_checked:
  system_test_observation T [] = NONE
Proof
  CONV_TAC cv_eval
QED

Theorem system_empty_code_unchecked:
  system_test_observation F [] = SOME ([], 5w, 17, 9, 23, 1, 19)
Proof
  CONV_TAC cv_eval
QED

(* Write storage, then fail, so success and rollback cannot look alike. *)
Theorem system_revert_checked:
  system_test_observation T
    [0x60w; 7w; 0x5fw; 0x55w; 0x5fw; 0x5fw; 0xfdw] = NONE
Proof
  CONV_TAC cv_eval
QED

Theorem system_revert_unchecked_rolls_back:
  system_test_observation F
    [0x60w; 7w; 0x5fw; 0x55w; 0x5fw; 0x5fw; 0xfdw] =
  SOME ([], 5w, 17, 9, 23, 1, 19)
Proof
  CONV_TAC cv_eval
QED

Theorem system_exception_checked:
  system_test_observation T [0x60w; 7w; 0x5fw; 0x55w; 0xfew] = NONE
Proof
  CONV_TAC cv_eval
QED

Theorem system_exception_unchecked_rolls_back:
  system_test_observation F [0x60w; 7w; 0x5fw; 0x55w; 0xfew] =
  SOME ([], 5w, 17, 9, 23, 1, 19)
Proof
  CONV_TAC cv_eval
QED

Definition system_oog_code_def:
  system_oog_code = [0x60w; 7w; 0x5fw; 0x55w; 0x7fw] ++
                    REPLICATE 32 0xffw ++ [0x51w]
End
val () = cv_auto_trans system_oog_code_def;

Theorem system_out_of_gas_checked:
  system_test_observation T system_oog_code = NONE
Proof
  CONV_TAC cv_eval
QED

Theorem system_out_of_gas_unchecked_rolls_back:
  system_test_observation F system_oog_code =
  SOME ([], 5w, 17, 9, 23, 1, 19)
Proof
  CONV_TAC cv_eval
QED

Definition system_output_words_def:
  system_output_words count result =
    OPTION_MAP (λ(output, accounts:evm_accounts, dom:domain_mode).
      GENLIST (λi. word_of_bytes T (0w:bytes32) (TAKE 32 (DROP (32 * i) output))) count)
      result
End
val () = cv_auto_trans system_output_words_def;

Theorem system_call_context:
  system_output_words 6 (system_test_call T
    [0x5aw; 0x5fw; 0x52w;
     0x33w; 0x60w; 0x20w; 0x52w;
     0x32w; 0x60w; 0x40w; 0x52w;
     0x34w; 0x60w; 0x60w; 0x52w;
     0x3aw; 0x60w; 0x80w; 0x52w;
     0x5fw; 0x35w; 0x60w; 0xa0w; 0x52w;
     0x60w; 0xc0w; 0x5fw; 0xf3w]) =
  SOME [29999998w; w2w system_address; w2w system_address; 0w; 1w; 42w]
Proof
  CONV_TAC cv_eval
QED

(* GAS; ADDRESS BALANCE POP; GAS computes a cold cost, then a warm one.
   Merely loading the contract's code must not warm its account. *)
Theorem system_target_starts_cold:
  system_output_words 2 (system_test_call T
    [0x5aw; 0x30w; 0x31w; 0x50w; 0x5aw; 0x90w; 0x03w; 0x5fw; 0x52w;
     0x5aw; 0x30w; 0x31w; 0x50w; 0x5aw; 0x90w; 0x03w; 0x60w; 0x20w; 0x52w;
     0x60w; 0x40w; 0x5fw; 0xf3w]) = SOME [2606w; 106w]
Proof
  CONV_TAC cv_eval
QED

Theorem system_domain_target_required:
  run_system_transaction F (Enforce empty_domain) 1 []
    (settlement_block 0x300w) (system_test_accounts [0w])
    withdrawal_request_contract [] = NONE
Proof
  CONV_TAC cv_eval
QED

Theorem system_domain_slot_required_even_unchecked:
  run_system_transaction F
    (Enforce (empty_domain with addresses := fINSERT withdrawal_request_contract fEMPTY))
    1 [] (settlement_block 0x300w)
    (system_test_accounts [0x5fw; 0x54w; 0w]) withdrawal_request_contract [] = NONE
Proof
  CONV_TAC cv_eval
QED

Theorem system_collects_reverted_accesses:
  OPTION_MAP (λ(_, _, dom). dom)
    (system_test_call F [0x5fw; 0x54w; 0x5fw; 0x5fw; 0xfdw]) =
  SOME (Collect (empty_domain with <|
    addresses := fINSERT withdrawal_request_contract fEMPTY;
    storageKeys := fINSERT (SK withdrawal_request_contract 0w) fEMPTY |>))
Proof
  CONV_TAC cv_eval
QED

Definition system_delegate_accounts_def:
  system_delegate_accounts =
    update_account 0x77w
      (empty_account_state with <| nonce := 1;
        code := [0x5aw; 0x60w; 0x77w; 0x31w; 0x50w; 0x5aw; 0x90w; 0x03w;
                 0x5fw; 0x52w; 0x60w; 0x20w; 0x5fw; 0xf3w] |>)
      (system_test_accounts ([0xefw; 1w; 0w] ++ REPLICATE 19 0w ++ [0x77w]))
End
val () = cv_auto_trans system_delegate_accounts_def;

Theorem system_resolves_and_warms_delegate:
  system_output_words 1
    (run_system_transaction T (Collect empty_domain) 1 []
      (settlement_block 0x300w) system_delegate_accounts
      withdrawal_request_contract []) = SOME [107w]
Proof
  CONV_TAC cv_eval
QED

(* CREATE succeeds with initcode PUSH1 1; SELFDESTRUCT. Returning the created
   address distinguishes successful creation/deletion from a failed CREATE. *)
Theorem system_finalizes_created_account_deletion:
  OPTION_MAP (λ(output, accounts, dom).
      (word_of_bytes T (0w:bytes32) output,
       (lookup_account (address_for_create withdrawal_request_contract 1) accounts).nonce,
       (lookup_account withdrawal_request_contract accounts).nonce))
    (system_test_call T
      [0x62w; 0x60w; 1w; 0xffw; 0x5fw; 0x52w;
       0x60w; 3w; 0x60w; 0x1dw; 0x5fw; 0xf0w;
       0x5fw; 0x52w; 0x60w; 0x20w; 0x5fw; 0xf3w]) =
  SOME (w2w (address_for_create withdrawal_request_contract 1), 0, 2)
Proof
  CONV_TAC cv_eval
QED

Theorem system_domain_delegate_required:
  run_system_transaction T
    (Enforce (empty_domain with addresses := fINSERT withdrawal_request_contract fEMPTY))
    1 [] (settlement_block 0x300w) system_delegate_accounts
    withdrawal_request_contract [] = NONE
Proof
  CONV_TAC cv_eval
QED

Definition system_block_parent_def:
  system_block_parent = settlement_block 0x300w with <|
    number := 0; timeStamp := 0; gasUsed := 500000; hash := 0x123w |>
End
val () = cv_auto_trans system_block_parent_def;

Definition system_block_def:
  system_block withdrawals withdrawal_data consolidation_data =
    settlement_block 0x300w with <|
      parentBeaconBlockRoot := 42w;
      withdrawals := withdrawals;
      withdrawalsRoot := word_of_bytes T 0w (withdrawals_root withdrawals);
      requestsHash := compute_requests_hash [] [withdrawal_data] [consolidation_data] |>
End
val () = cv_auto_trans system_block_def;

Definition system_block_accounts_def:
  system_block_accounts withdrawal_code consolidation_code =
    update_account beacon_roots_address
      (empty_account_state with <| nonce := 1;
        code := [0x5fw; 0x35w; 0x5fw; 0x55w; 0w] |>)
    (update_account history_storage_address
      (empty_account_state with <| nonce := 1;
        code := [0x5fw; 0x35w; 0x5fw; 0x55w; 0w] |>)
    (update_account consolidation_request_contract
      (empty_account_state with <| nonce := 1; code := consolidation_code |>)
      (system_test_accounts withdrawal_code)))
End
val () = cv_auto_trans system_block_accounts_def;

Definition system_block_observation_def:
  system_block_observation accounts blk =
    OPTION_MAP (λ(rs, accounts, dom).
      (LENGTH rs,
       MAP (λaddr. lookup_storage 0w (lookup_account addr accounts).storage)
         [beacon_roots_address; history_storage_address;
          withdrawal_request_contract; consolidation_request_contract],
       (lookup_account withdrawal_request_contract accounts).balance))
      (run_block (Collect empty_domain) 1 [system_block_parent.hash]
        system_block_parent accounts blk)
End
val () = cv_auto_trans system_block_observation_def;

(* Beacon/history use their actual calldata; request calls observe withdrawals. *)
Theorem system_block_calls_after_withdrawals:
  system_block_observation
    (system_block_accounts [0x47w; 0x5fw; 0x55w; 0w] [0w])
    (system_block [<| withdrawalIndex := 0; validatorIndex := 0;
                     withdrawalAddress := withdrawal_request_contract;
                     withdrawalAmount := 2 |>] [] []) =
  SOME (0, [42w; 0x123w; 2000000023w; 0w], 2000000023)
Proof
  CONV_TAC cv_eval
QED

(* The requests hash commits to raw returned bytes, including short outputs. *)
Theorem system_block_hashes_modified_return_data:
  system_block_observation
    (system_block_accounts
      [0x60w; 0xaaw; 0x5fw; 0x53w; 0x60w; 1w; 0x5fw; 0xf3w]
      [0x60w; 0xbbw; 0x5fw; 0x53w; 0x60w; 1w; 0x5fw; 0xf3w])
    (system_block [] [0xaaw] [0xbbw]) =
  SOME (0, [42w; 0x123w; 5w; 0w], 23)
Proof
  CONV_TAC cv_eval
QED

Theorem system_block_rejects_failed_request_call:
  system_block_observation (system_block_accounts [0xfew] [0w])
    (system_block [] [] []) = NONE
Proof
  CONV_TAC cv_eval
QED

Theorem system_block_ignores_and_rolls_back_failed_beacon_call:
  system_block_observation
    (update_account beacon_roots_address
      (empty_account_state with <| nonce := 1;
        code := [0x60w; 7w; 0x5fw; 0x55w; 0x5fw; 0x5fw; 0xfdw];
        storage := update_storage 0w 9w empty_storage |>)
      (system_block_accounts [0w] [0w]))
    (system_block [] [] []) =
  SOME (0, [9w; 0x123w; 5w; 0w], 23)
Proof
  CONV_TAC cv_eval
QED

Theorem system_block_rejects_empty_request_code:
  system_block_observation (system_block_accounts [0w] [])
    (system_block [] [] []) = NONE
Proof
  CONV_TAC cv_eval
QED
