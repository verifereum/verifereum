Theory vfmChainId
Ancestors vfmBlockDecode
Libs cv_transLib wordsLib

(* The decoder accepts a transaction only for the chain it was signed for.
   The signature values are arbitrary but valid (r is the x-coordinate of the
   secp256k1 generator), so each transaction recovers some sender. *)

Definition chain_test_r_def:
  chain_test_r =
  0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798n
End
val () = cv_auto_trans chain_test_r_def;

(* A legacy transaction with EIP-155 v = 35 + 2 * 5 + 0, i.e. chain 5. *)
Definition chain_test_legacy_def:
  chain_test_legacy =
  RLPL (MAP rlp_number [0; 1; 21000] ++ [RLPB (REPLICATE 20 1w)] ++
        MAP rlp_number [0] ++ [RLPB []] ++
        MAP rlp_number [45; chain_test_r; 1])
End
val () = cv_auto_trans chain_test_legacy_def;

(* A type-1 transaction whose chain ID field is 5. *)
Definition chain_test_typed_def:
  chain_test_typed =
  RLPL (MAP rlp_number [5; 0; 1; 21000] ++ [RLPB (REPLICATE 20 1w)] ++
        MAP rlp_number [0] ++ [RLPB []; RLPL []] ++
        MAP rlp_number [0; chain_test_r; 1])
End
val () = cv_auto_trans chain_test_typed_def;

Definition chain_test_decodes_def:
  chain_test_decodes chainId =
  (IS_SOME (transaction_from_rlp chainId 0 chain_test_legacy),
   IS_SOME (transaction1_from_rlp chainId chain_test_typed))
End
val () = cv_auto_trans chain_test_decodes_def;

Theorem chain_id_signed_chain:
  chain_test_decodes 5 = (T, T)
Proof
  CONV_TAC cv_eval
QED

Theorem chain_id_other_chain:
  chain_test_decodes 1 = (F, F)
Proof
  CONV_TAC cv_eval
QED
