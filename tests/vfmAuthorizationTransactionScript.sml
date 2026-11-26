Theory vfmAuthorizationTransaction
Ancestors byte vfmSettlement vfmBlockDecode
Libs cv_transLib wordsLib

(* Deterministic ECDSA fixtures: sender private key 1, authority private key 2.
   Each outer signature covers 0x04 || RLP of all ten unsigned fields, including
   the authorization. Fees are priority 1 / max 3 with block base fee 1. *)
Definition auth_tx_sender_def:
  auth_tx_sender : address = 0x7e5f4552091a69125d5dfcb7b8c2659029395bdfw
End
val () = cv_auto_trans auth_tx_sender_def;

Definition auth_tx_authority_def:
  auth_tx_authority : address = 0x2b5ad5c4795c026514f8317c7a215e218dccd6cfw
End
val () = cv_auto_trans auth_tx_authority_def;

Definition auth_tx_authorization_def:
  auth_tx_authorization nonce parity r s =
    RLPL [rlp_number 1; RLPB (word_to_bytes (0x200w:address) T);
          rlp_number nonce; rlp_number parity; rlp_number r; rlp_number s]
End
val () = cv_auto_trans $ REWRITE_RULE [GSYM word_to_bytes_be_def]
  auth_tx_authorization_def;

Definition auth_tx_rlp_def:
  auth_tx_rlp parity v r s =
    RLPL (MAP rlp_number [1; 0; 1; 3; 50000] ++
      [RLPB (word_to_bytes (0x200w:address) T); rlp_number 0;
       RLPB []; RLPL []; RLPL [auth_tx_authorization 0 parity 1 1]] ++
      MAP rlp_number [v; r; s])
End
val () = cv_auto_trans $ REWRITE_RULE [GSYM word_to_bytes_be_def] auth_tx_rlp_def;

Definition auth_tx_parity256_def:
  auth_tx_parity256 = auth_tx_rlp 256 0
    0x78da927a780a4e78e3ce57629ecfd7ccca70eb2d67b08e7e9d51198cee1f4e1en
    0x7283856fea858cf5bad41e81e12880ae84715a89a9dd0507d93e22de69dc2849n
End
val () = cv_auto_trans auth_tx_parity256_def;

(* Check the rejected fixture's outer signature independently, so a bad
   signature cannot make the rejection regression pass for the wrong reason. *)
Theorem authorization_parity256_outer_signature_valid:
  verify_tx_signature 4w (TAKE 10 (dest_RLPL auth_tx_parity256))
    (EL 10 (dest_RLPL auth_tx_parity256))
    (EL 11 (dest_RLPL auth_tx_parity256))
    (EL 12 (dest_RLPL auth_tx_parity256)) = SOME auth_tx_sender
Proof
  simp_tac (srw_ss()) [auth_tx_parity256_def, auth_tx_rlp_def]
  \\ CONV_TAC cv_eval
QED

Definition auth_tx_accounts_def:
  auth_tx_accounts = update_account auth_tx_sender
    (empty_account_state with balance := 1000000) empty_accounts
End
val () = cv_auto_trans auth_tx_accounts_def;

(* Include the public typed-byte dispatch, then run against a funded nonce-0
   sender and an empty, non-null destination with enough gas for one auth. *)
Definition auth_tx_observation_def:
  auth_tx_observation rlp =
    case transaction_from_rlp 1 1 (RLPB (4w :: rlp_encode rlp)) of
      NONE => NONE
    | SOME tx => OPTION_MAP (λ(tr, accounts).
        (tx.from, tx.to, tx.nonce, tx.gasLimit, tx.gasPrice, tx.maxFeePerGas,
         tr.result, tr.gasUsed,
         (lookup_account auth_tx_sender accounts).balance,
         (lookup_account auth_tx_sender accounts).nonce,
         (lookup_account 0w accounts).nonce,
         (lookup_account 0w accounts).code))
        (run_transaction (Collect empty_domain) F 1 []
          (settlement_block 0x300w) auth_tx_accounts tx)
End
val () = cv_auto_trans auth_tx_observation_def;

(* Out-of-bounds auths invalidate both the type-4 decoder and typed-byte path. *)
Theorem authorization_parity256_transaction_rejected:
  transaction4_from_rlp 1 1 auth_tx_parity256 = NONE ∧
  transaction_from_rlp 1 1
    (RLPB (4w :: rlp_encode auth_tx_parity256)) = NONE
Proof
  CONV_TAC cv_eval
QED

Theorem authorization_parity2_transaction_skips:
  auth_tx_observation (auth_tx_rlp 2 1
    0x4e679bdc9736dfddc01ee2d62c098358f5d81a1efcedefcc476a68e50eb2e0b7n
    0x7b43207c53c8e004ebd778d42d1c79d1b2e3329e7f7ca9c9dd43b2cdfd4ce44cn) =
  SOME (auth_tx_sender, SOME 0x200w, 0, 50000, 2, SOME 3,
        NONE, 46000, 908000, 1, 0, [])
Proof
  CONV_TAC cv_eval
QED

Theorem authorization_parity255_transaction_skips:
  auth_tx_observation (auth_tx_rlp 255 1
    0x8253d94b438a92e2b1a210bd3c6dedb1d46357b5dfb36face0feefacb93bfaf7n
    0x82528c8d545bbe1a016ce603ed33ba2c70df77205b32ec4a6cd8b0a3bd71d1an) =
  SOME (auth_tx_sender, SOME 0x200w, 0, 50000, 2, SOME 3,
        NONE, 46000, 908000, 1, 0, [])
Proof
  CONV_TAC cv_eval
QED

Definition auth_tx_valid_authorization_def:
  auth_tx_valid_authorization = auth_tx_authorization 0 1
    0x1e9e8839d2201709330d218c0e7e08035568e151f058167875413e2cbcf6b476n
    0x1855e76592da052fc8b5d4e8e1919a9e4b978bbdcf84ffc7398547f24c82f895n
End
val () = cv_auto_trans auth_tx_valid_authorization_def;

Theorem authorization_valid_signature_decodes:
  authorization_from_rlp auth_tx_valid_authorization =
  SOME <| authority := auth_tx_authority; delegate := 0x200w;
          authChainId := 1; authNonce := 0;
          authS :=
            0x1855e76592da052fc8b5d4e8e1919a9e4b978bbdcf84ffc7398547f24c82f895n |>
Proof
  CONV_TAC cv_eval
QED

Definition auth_tx_process_observation_def:
  auth_tx_process_observation nonce rlp =
    let accounts = update_account auth_tx_authority
          (empty_account_state with <| balance := 17; nonce := nonce |>)
          auth_tx_accounts in
    case authorization_from_rlp rlp of NONE => NONE | SOME auth =>
    let (accounts', accesses, refund) = process_authorization 1 auth
          (accounts, <| addresses := fEMPTY; storageKeys := fEMPTY |>, 7) in
    SOME (auth.authority,
          (lookup_account auth_tx_authority accounts').nonce,
          (lookup_account auth_tx_authority accounts').code,
          accesses, refund, (lookup_account auth_tx_authority accounts').balance)
End
val () = cv_auto_trans auth_tx_process_observation_def;

Theorem authorization_valid_signature_applies:
  auth_tx_process_observation 0 auth_tx_valid_authorization =
  SOME (auth_tx_authority, 1, make_delegation 0x200w,
        <| addresses := fINSERT auth_tx_authority fEMPTY; storageKeys := fEMPTY |>,
        12507, 17)
Proof
  CONV_TAC cv_eval
QED

(* A real signature with the matching account nonce isolates the nonce-limit
   skip from signature recovery and nonce-mismatch failures. *)
Theorem authorization_max_nonce_decodes_but_skips:
  auth_tx_process_observation (2 ** 64 - 1)
    (auth_tx_authorization (2 ** 64 - 1) 0
      0x5e88df911951970847c3366142b3643c5d88610abb48948fbe305ad4c9622e4fn
      0x67f0ffe4dd9e1c4f4ff7b28d47655e7dc30d6399d3cee8a6913a430689e90462n) =
  SOME (auth_tx_authority, 2 ** 64 - 1, [],
        <| addresses := fEMPTY; storageKeys := fEMPTY |>, 7, 17)
Proof
  CONV_TAC cv_eval
QED
