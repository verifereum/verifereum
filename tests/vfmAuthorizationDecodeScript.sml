Theory vfmAuthorizationDecode
Ancestors vfmBlockDecode
Libs cv_transLib wordsLib

(* Numeric field bounds, not integer-encoding canonicality or signature validity. *)
Definition auth_bounds_rlp_def:
  auth_bounds_rlp chainId address nonce parity r s =
    RLPL [rlp_number chainId; RLPB address; rlp_number nonce;
          rlp_number parity; rlp_number r; rlp_number s]
End
val () = cv_auto_trans auth_bounds_rlp_def;

Theorem authorization_numeric_upper_bounds:
  authorization_from_rlp
    (auth_bounds_rlp (2 ** 256) (REPLICATE 20 1w) 0 2 1 1) = NONE ∧
  authorization_from_rlp
    (auth_bounds_rlp 1 (REPLICATE 20 1w) (2 ** 64) 2 1 1) = NONE ∧
  authorization_from_rlp
    (auth_bounds_rlp 1 (REPLICATE 20 1w) 0 (2 ** 8) 1 1) = NONE ∧
  authorization_from_rlp
    (auth_bounds_rlp 1 (REPLICATE 20 1w) 0 2 (2 ** 256) 1) = NONE ∧
  authorization_from_rlp
    (auth_bounds_rlp 1 (REPLICATE 20 1w) 0 2 1 (2 ** 256)) = NONE
Proof
  CONV_TAC cv_eval
QED

Theorem authorization_address_lengths:
  authorization_from_rlp (auth_bounds_rlp 1 [] 0 2 1 1) = NONE ∧
  authorization_from_rlp
    (auth_bounds_rlp 1 (REPLICATE 19 1w) 0 2 1 1) = NONE ∧
  authorization_from_rlp
    (auth_bounds_rlp 1 (REPLICATE 21 1w) 0 2 1 1) = NONE ∧
  authorization_from_rlp
    (auth_bounds_rlp 1 (REPLICATE 32 1w) 0 2 1 1) = NONE
Proof
  CONV_TAC cv_eval
QED

(* Maximal in-bounds fields still decode, despite failing authorization recovery.
   Inspect the numeric values so truncation cannot masquerade as acceptance. *)
Theorem authorization_maximum_fields_decode:
  authorization_from_rlp
    (auth_bounds_rlp (2 ** 256 - 1) (REPLICATE 20 0xffw)
       (2 ** 64 - 1) 255 (2 ** 256 - 1) (2 ** 256 - 1)) =
  SOME <| authority := 0w; delegate := 0xffffffffffffffffffffffffffffffffffffffffw;
          authChainId := 2 ** 256 - 1; authNonce := 2 ** 64 - 1;
          authS := 2 ** 256 - 1 |>
Proof
  CONV_TAC cv_eval
QED

Theorem authorization_zero_fields_decode:
  authorization_from_rlp (auth_bounds_rlp 0 (REPLICATE 20 0w) 0 0 0 0) =
  SOME <| authority := 0w; delegate := 0w; authChainId := 0;
          authNonce := 0; authS := 0 |>
Proof
  CONV_TAC cv_eval
QED
