Theory vfmTypedDecode
Ancestors vfmBlockDecode
Libs cv_transLib wordsLib

(* Osaka 97166d93ff7d0250e1528cf42bebb9814f131476, transactions.py,
   blocks.py and fork_types.py. Uint fields are deliberately NOT bounded.
   Signed fixtures use private key 1 and ECDSA nonce 1 (fixtures only),
   with low-s normalization; their sender is checked below. Each malformed
   payload was signed AFTER introducing the malformed field. *)
Definition typed_test_valid_def:
  typed_test_valid = RLPB
    [2w; 248w; 99w; 1w; 128w; 1w; 2w; 131w; 1w; 134w; 160w; 148w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 128w; 128w; 192w; 1w; 160w; 121w; 190w; 102w; 126w; 249w; 220w; 187w; 172w; 85w; 160w; 98w; 149w; 206w; 135w; 11w; 7w; 2w; 155w; 252w; 219w; 45w; 206w; 40w; 217w; 89w; 242w; 129w; 91w; 22w; 248w; 23w; 152w; 160w; 29w; 111w; 217w; 215w; 192w; 109w; 171w; 247w; 184w; 135w; 252w; 135w; 29w; 101w; 6w; 230w; 81w; 232w; 76w; 98w; 170w; 249w; 30w; 72w; 191w; 241w; 114w; 53w; 163w; 34w; 26w; 59w]
End
val () = cv_auto_trans typed_test_valid_def;

Definition typed_test_short_destination_def:
  typed_test_short_destination = RLPB
    [2w; 248w; 98w; 1w; 128w; 1w; 2w; 131w; 1w; 134w; 160w; 147w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 128w; 128w; 192w; 1w; 160w; 121w; 190w; 102w; 126w; 249w; 220w; 187w; 172w; 85w; 160w; 98w; 149w; 206w; 135w; 11w; 7w; 2w; 155w; 252w; 219w; 45w; 206w; 40w; 217w; 89w; 242w; 129w; 91w; 22w; 248w; 23w; 152w; 160w; 36w; 1w; 128w; 60w; 128w; 178w; 72w; 51w; 107w; 173w; 115w; 53w; 73w; 165w; 158w; 114w; 113w; 30w; 38w; 133w; 240w; 232w; 223w; 35w; 121w; 213w; 117w; 46w; 57w; 238w; 155w; 129w]
End
val () = cv_auto_trans typed_test_short_destination_def;

Definition typed_test_zero_nonce_def:
  typed_test_zero_nonce = RLPB
    [2w; 248w; 99w; 1w; 0w; 1w; 2w; 131w; 1w; 134w; 160w; 148w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 128w; 128w; 192w; 1w; 160w; 121w; 190w; 102w; 126w; 249w; 220w; 187w; 172w; 85w; 160w; 98w; 149w; 206w; 135w; 11w; 7w; 2w; 155w; 252w; 219w; 45w; 206w; 40w; 217w; 89w; 242w; 129w; 91w; 22w; 248w; 23w; 152w; 160w; 28w; 176w; 34w; 4w; 167w; 235w; 16w; 57w; 88w; 210w; 206w; 244w; 41w; 71w; 26w; 176w; 149w; 203w; 220w; 127w; 105w; 143w; 138w; 66w; 15w; 130w; 255w; 196w; 180w; 184w; 113w; 216w]
End
val () = cv_auto_trans typed_test_zero_nonce_def;

Definition typed_test_type1_creation_def:
  typed_test_type1_creation = RLPB
    [1w; 248w; 78w; 1w; 128w; 1w; 131w; 1w; 134w; 160w; 128w; 128w; 128w; 192w; 128w; 160w; 121w; 190w; 102w; 126w; 249w; 220w; 187w; 172w; 85w; 160w; 98w; 149w; 206w; 135w; 11w; 7w; 2w; 155w; 252w; 219w; 45w; 206w; 40w; 217w; 89w; 242w; 129w; 91w; 22w; 248w; 23w; 152w; 160w; 69w; 170w; 202w; 149w; 243w; 110w; 155w; 77w; 8w; 86w; 151w; 98w; 68w; 65w; 14w; 11w; 60w; 137w; 111w; 17w; 23w; 64w; 12w; 128w; 5w; 250w; 72w; 225w; 75w; 14w; 99w; 249w]
End
val () = cv_auto_trans typed_test_type1_creation_def;

Definition typed_test_type2_creation_def:
  typed_test_type2_creation = RLPB
    [2w; 248w; 79w; 1w; 128w; 1w; 2w; 131w; 1w; 134w; 160w; 128w; 128w; 128w; 192w; 1w; 160w; 121w; 190w; 102w; 126w; 249w; 220w; 187w; 172w; 85w; 160w; 98w; 149w; 206w; 135w; 11w; 7w; 2w; 155w; 252w; 219w; 45w; 206w; 40w; 217w; 89w; 242w; 129w; 91w; 22w; 248w; 23w; 152w; 160w; 123w; 252w; 45w; 102w; 167w; 75w; 187w; 31w; 184w; 154w; 223w; 40w; 113w; 34w; 178w; 97w; 213w; 90w; 127w; 244w; 181w; 161w; 231w; 191w; 95w; 161w; 52w; 141w; 103w; 115w; 23w; 58w]
End
val () = cv_auto_trans typed_test_type2_creation_def;

Definition typed_test_type3_empty_destination_def:
  typed_test_type3_empty_destination = RLPB
    [3w; 248w; 81w; 1w; 128w; 1w; 2w; 131w; 1w; 134w; 160w; 128w; 128w; 128w; 192w; 1w; 192w; 1w; 160w; 121w; 190w; 102w; 126w; 249w; 220w; 187w; 172w; 85w; 160w; 98w; 149w; 206w; 135w; 11w; 7w; 2w; 155w; 252w; 219w; 45w; 206w; 40w; 217w; 89w; 242w; 129w; 91w; 22w; 248w; 23w; 152w; 160w; 116w; 98w; 109w; 112w; 105w; 162w; 26w; 229w; 1w; 231w; 214w; 75w; 234w; 56w; 86w; 226w; 255w; 84w; 85w; 88w; 194w; 116w; 141w; 110w; 62w; 107w; 208w; 231w; 203w; 36w; 31w; 120w]
End
val () = cv_auto_trans typed_test_type3_empty_destination_def;

Definition typed_test_type4_empty_destination_def:
  typed_test_type4_empty_destination = RLPB
    [4w; 248w; 107w; 1w; 128w; 1w; 2w; 131w; 1w; 134w; 160w; 128w; 128w; 128w; 192w; 219w; 218w; 128w; 148w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 128w; 128w; 1w; 1w; 1w; 160w; 121w; 190w; 102w; 126w; 249w; 220w; 187w; 172w; 85w; 160w; 98w; 149w; 206w; 135w; 11w; 7w; 2w; 155w; 252w; 219w; 45w; 206w; 40w; 217w; 89w; 242w; 129w; 91w; 22w; 248w; 23w; 152w; 160w; 8w; 8w; 125w; 135w; 57w; 165w; 99w; 56w; 24w; 87w; 232w; 77w; 221w; 18w; 218w; 204w; 15w; 135w; 80w; 50w; 50w; 94w; 137w; 40w; 179w; 206w; 63w; 149w; 125w; 131w; 127w; 7w]
End
val () = cv_auto_trans typed_test_type4_empty_destination_def;

Definition typed_test_core_def:
  typed_test_core = MAP rlp_number [1; 0; 1; 2; 100000] ++
    [RLPB (REPLICATE 20 0w); rlp_number 0; RLPB []; RLPL []]
End
val () = cv_auto_trans typed_test_core_def;

Definition typed_test_header_def:
  typed_test_header =
    [RLPB (REPLICATE 32 0w); RLPB (word_to_bytes empty_ommer_hash T);
     RLPB (REPLICATE 20 0w); RLPB (REPLICATE 32 0w);
     RLPB (REPLICATE 32 0w); RLPB (REPLICATE 32 0w);
     RLPB (REPLICATE 256 0w); rlp_number 0; rlp_number 1;
     rlp_number 100000; rlp_number 0; rlp_number 1; RLPB [];
     RLPB (REPLICATE 32 0w); RLPB (REPLICATE 8 0w);
     rlp_number 1; RLPB (REPLICATE 32 0w); rlp_number 0;
     rlp_number 0; RLPB (REPLICATE 32 0w); RLPB (REPLICATE 32 0w)]
End
val () = cv_auto_trans $ REWRITE_RULE [GSYM byteTheory.word_to_bytes_be_def]
  typed_test_header_def;

Definition typed_test_sign_def:
  typed_test_sign ls = RLPL (ls ++ MAP rlp_number
    [0; 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798; 1])
End
val () = cv_auto_trans typed_test_sign_def;

Definition typed_test_legacy_def:
  typed_test_legacy = MAP rlp_number [0; 1; 100000] ++
    [RLPB (REPLICATE 20 0w); rlp_number 0; RLPB []] ++
    MAP rlp_number [27; 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798; 1]
End
val () = cv_auto_trans typed_test_legacy_def;

Definition typed_test_auth_def:
  typed_test_auth = [rlp_number 0; RLPB (REPLICATE 20 0w);
                    rlp_number 0; rlp_number 0; rlp_number 1; rlp_number 1]
End
val () = cv_auto_trans typed_test_auth_def;

Definition typed_test_blob_def:
  typed_test_blob = typed_test_core ++
    [rlp_number 1; RLPL [RLPB (REPLICATE 32 1w)]]
End
val () = cv_auto_trans typed_test_blob_def;

Definition typed_test_setcode_def:
  typed_test_setcode = typed_test_core ++ [RLPL [RLPL typed_test_auth]]
End
val () = cv_auto_trans typed_test_setcode_def;

Definition typed_test_is_sender_def:
  typed_test_is_sender tx ⇔
    tx.from = 0x7e5f4552091a69125d5dfcb7b8c2659029395bdfw
End
val () = cv_auto_trans typed_test_is_sender_def;

Definition typed_test_verify_payload_def:
  typed_test_verify_payload rlp =
    case dest_RLPL rlp of
      [a; b; c; d; e; f; g; h; i; y; r; s] =>
        verify_tx_signature 2w [a; b; c; d; e; f; g; h; i] y r s
    | _ => NONE
End
val () = cv_auto_trans typed_test_verify_payload_def;

Definition typed_test_signature_minimal_payload_def:
  typed_test_signature_minimal_payload rlp =
    case dest_RLPL rlp of
      [a; b; c; d; e; f; g; h; i; y; r; s] =>
        let payload = [a; b; c; d; e; f; g; h; i] in
        verify_tx_signature 2w payload (RLPB (0w :: dest_RLPB y)) r s = NONE ∧
        verify_tx_signature 2w payload y (RLPB (0w :: dest_RLPB r)) s = NONE ∧
        verify_tx_signature 2w payload y r (RLPB (0w :: dest_RLPB s)) = NONE
    | _ => F
End
val () = cv_auto_trans typed_test_signature_minimal_payload_def;

(* Run every assertion before raising, so the pre-fix run records independent
   failures instead of hiding all but the first regression. Successful checks
   are saved as kernel-checked theorems. *)
val typed_test_failures = ref ([] : string list);
fun typed_check (name, tm) =
  let
    val def = new_definition (name ^ "_check_def",
      mk_eq (mk_var (name ^ "_check", type_of tm), tm))
    val () = cv_auto_trans def
    val th = cv_eval (lhs (concl def))
  in
    if rhs (concl th) ~~ ``T`` then
      (save_thm (name, REWRITE_RULE [def] (EQT_ELIM th));
       print ("PASS " ^ name ^ "\n"))
    else (typed_test_failures := name :: !typed_test_failures;
          print ("FAIL " ^ name ^ ": " ^ term_to_string (rhs (concl th)) ^ "\n"))
  end;

val () = typed_check ("typed_signed_valid_sender",
  ``(case transaction_from_rlp 1 1 typed_test_valid of NONE => F | SOME tx => typed_test_is_sender tx)``);

val () = typed_check ("typed_signed_rejects_short_destination",
  ``transaction_from_rlp 1 1 typed_test_short_destination = NONE``);

val () = typed_check ("typed_signed_rejects_zero_nonce",
  ``transaction_from_rlp 1 1 typed_test_zero_nonce = NONE``);

val () = typed_check ("typed_signed_rejects_type3_empty_destination",
  ``transaction_from_rlp 1 1 typed_test_type3_empty_destination = NONE``);

val () = typed_check ("typed_signed_rejects_type4_empty_destination",
  ``transaction_from_rlp 1 1 typed_test_type4_empty_destination = NONE``);

val () = typed_check ("typed_signed_accepts_type1_creation",
  ``IS_SOME (transaction_from_rlp 1 1 typed_test_type1_creation)``);

val () = typed_check ("typed_signed_accepts_type2_creation",
  ``IS_SOME (transaction_from_rlp 1 1 typed_test_type2_creation)``);

val () = typed_check ("typed_core_valid",
  ``IS_SOME (decode_eip1559_core typed_test_core)``);

val () = typed_check ("typed_core_destination_widths",
  ``EVERY (λn. IS_NONE (decode_eip1559_core (LUPDATE (RLPB (REPLICATE n 1w)) 5 typed_test_core))) [1; 19; 21; 32]``);

val () = typed_check ("typed_core_minimal_integers",
  ``EVERY (λi. IS_NONE (decode_eip1559_core (LUPDATE (RLPB [0w]) i typed_test_core))) [1; 2; 3; 4; 6]``);

val () = typed_check ("typed_core_u256_bounds",
  ``EVERY (λi. IS_NONE (decode_eip1559_core (LUPDATE (rlp_number (2 ** 256)) i typed_test_core))) [1; 6]``);

val () = typed_check ("typed_core_unbounded_uint",
  ``IS_SOME (decode_eip1559_core (LUPDATE (rlp_number (2 ** 300)) 4 (LUPDATE (rlp_number (2 ** 300)) 3 (LUPDATE (rlp_number (2 ** 299)) 2 typed_test_core))))``);

val () = typed_check ("typed_access_valid",
  ``IS_SOME (access_list_entry_from_rlp (RLPL [RLPB (REPLICATE 20 0w); RLPL [RLPB (REPLICATE 32 0w)]]))``);

val () = typed_check ("typed_access_address_width",
  ``EVERY (λn. IS_NONE (access_list_entry_from_rlp (RLPL [RLPB (REPLICATE n 0w); RLPL []]))) [0; 19; 21; 32]``);

val () = typed_check ("typed_access_slot_width",
  ``EVERY (λn. IS_NONE (access_list_entry_from_rlp (RLPL [RLPB (REPLICATE 20 0w); RLPL [RLPB (REPLICATE n 0w)]]))) [0; 31; 33]``);

val () = typed_check ("typed_withdrawal_valid",
  ``IS_SOME (withdrawal_from_rlp (RLPL [rlp_number 0; rlp_number 0; RLPB (REPLICATE 20 0w); rlp_number 0]))``);

val () = typed_check ("typed_withdrawal_address_width",
  ``IS_NONE (withdrawal_from_rlp (RLPL (LUPDATE (RLPB (REPLICATE 19 0w)) 2 [rlp_number 0; rlp_number 0; RLPB (REPLICATE 20 0w); rlp_number 0])))``);

val () = typed_check ("typed_withdrawal_minimal",
  ``EVERY (λi. IS_NONE (withdrawal_from_rlp (RLPL (LUPDATE (RLPB [0w]) i [rlp_number 0; rlp_number 0; RLPB (REPLICATE 20 0w); rlp_number 0])))) [0; 1; 3]``);

val () = typed_check ("typed_withdrawal_u64_bound",
  ``EVERY (λi. IS_NONE (withdrawal_from_rlp (RLPL (LUPDATE (rlp_number (2 ** 64)) i [rlp_number 0; rlp_number 0; RLPB (REPLICATE 20 0w); rlp_number 0])))) [0; 1; 3]``);

val () = typed_check ("typed_header_valid",
  ``IS_SOME (block_header_from_rlp (RLPL typed_test_header))``);

val () = typed_check ("typed_header_width_32",
  ``EVERY (λi. IS_NONE (block_header_from_rlp (RLPL (LUPDATE (RLPB (REPLICATE 31 0w)) i typed_test_header)))) [0; 3; 4; 5; 13; 16; 19; 20]``);

val () = typed_check ("typed_header_width_20",
  ``EVERY (λi. IS_NONE (block_header_from_rlp (RLPL (LUPDATE (RLPB (REPLICATE 19 0w)) i typed_test_header)))) [2]``);

val () = typed_check ("typed_header_width_256",
  ``EVERY (λi. IS_NONE (block_header_from_rlp (RLPL (LUPDATE (RLPB (REPLICATE 255 0w)) i typed_test_header)))) [6]``);

val () = typed_check ("typed_header_minimal_integers",
  ``EVERY (λi. IS_NONE (block_header_from_rlp (RLPL (LUPDATE (RLPB [0w]) i typed_test_header)))) [7; 8; 9; 10; 11; 15; 17; 18]``);

val () = typed_check ("typed_header_u64_bounds",
  ``EVERY (λi. IS_NONE (block_header_from_rlp (RLPL (LUPDATE (rlp_number (2 ** 64)) i typed_test_header)))) [17; 18]``);

val () = typed_check ("typed_header_timestamp_bound",
  ``IS_NONE (block_header_from_rlp (RLPL (LUPDATE (rlp_number (2 ** 256)) 11 typed_test_header)))``);

val () = typed_check ("typed_header_unbounded_uint",
  ``EVERY (λi. IS_SOME (block_header_from_rlp (RLPL (LUPDATE (rlp_number (2 ** 300)) i typed_test_header)))) [8; 9; 10; 15]``);

val () = typed_check ("typed_signed_short_destination_signature",
  ``OPTION_BIND (rlp_decode_chunks [DROP 1 (dest_RLPB typed_test_short_destination)])
      typed_test_verify_payload =
    SOME 0x7e5f4552091a69125d5dfcb7b8c2659029395bdfw``);

val () = typed_check ("typed_signed_zero_nonce_signature",
  ``OPTION_BIND (rlp_decode_chunks [DROP 1 (dest_RLPB typed_test_zero_nonce)])
      typed_test_verify_payload =
    SOME 0x7e5f4552091a69125d5dfcb7b8c2659029395bdfw``);

val () = typed_check ("typed_core_nonzero_leading_zero",
  ``EVERY (λi. IS_NONE (decode_eip1559_core (LUPDATE (RLPB [0w; 1w]) i typed_test_core))) [1; 2; 3; 4; 6]``);

val () = typed_check ("typed_core_max_u256",
  ``EVERY (λi. IS_SOME (decode_eip1559_core (LUPDATE (rlp_number (2 ** 256 - 1)) i typed_test_core))) [1; 6]``);

val () = typed_check ("typed_legacy_valid",
  ``IS_SOME (transaction_from_rlp 1 1 (RLPL typed_test_legacy))``);

val () = typed_check ("typed_legacy_destination_width",
  ``EVERY (λn. IS_NONE (transaction_from_rlp 1 1 (RLPL (LUPDATE (RLPB (REPLICATE n 0w)) 3 typed_test_legacy)))) [1; 19; 21]``);

val () = typed_check ("typed_legacy_minimal_integers",
  ``EVERY (λi. IS_NONE (transaction_from_rlp 1 1 (RLPL (LUPDATE (RLPB [0w; 1w]) i typed_test_legacy)))) [0; 1; 2; 4; 6; 7; 8]``);

val () = typed_check ("typed_legacy_u256_bounds",
  ``EVERY (λi. IS_NONE (transaction_from_rlp 1 1 (RLPL (LUPDATE (rlp_number (2 ** 256)) i typed_test_legacy)))) [0; 4; 6; 7; 8]``);

val () = typed_check ("typed_legacy_unbounded_uint",
  ``EVERY (λi. IS_SOME (transaction_from_rlp 1 1 (RLPL (LUPDATE (rlp_number (2 ** 300)) i typed_test_legacy)))) [1; 2]``);

val () = typed_check ("typed_type1_chain_bound",
  ``IS_NONE (transaction1_from_rlp (2 ** 64)
    (typed_test_sign (MAP rlp_number [2 ** 64; 0; 1; 100000] ++
      [RLPB (REPLICATE 20 0w); rlp_number 0; RLPB []; RLPL []])))``);

val () = typed_check ("typed_type1_max_chain",
  ``IS_SOME (transaction1_from_rlp (2 ** 64 - 1)
    (typed_test_sign (MAP rlp_number [2 ** 64 - 1; 0; 1; 100000] ++
      [RLPB (REPLICATE 20 0w); rlp_number 0; RLPB []; RLPL []])))``);

val () = typed_check ("typed_type2_chain_bound",
  ``IS_NONE (transaction2_from_rlp (2 ** 64) 1 (typed_test_sign (LUPDATE (rlp_number (2 ** 64)) 0 typed_test_core)))``);

val () = typed_check ("typed_type2_max_chain",
  ``IS_SOME (transaction2_from_rlp (2 ** 64 - 1) 1 (typed_test_sign (LUPDATE (rlp_number (2 ** 64 - 1)) 0 typed_test_core)))``);

val () = typed_check ("typed_type3_chain_bound",
  ``IS_NONE (transaction3_from_rlp (2 ** 64) 1 (typed_test_sign (LUPDATE (rlp_number (2 ** 64)) 0 typed_test_blob)))``);

val () = typed_check ("typed_type3_max_chain",
  ``IS_SOME (transaction3_from_rlp (2 ** 64 - 1) 1 (typed_test_sign (LUPDATE (rlp_number (2 ** 64 - 1)) 0 typed_test_blob)))``);

val () = typed_check ("typed_type4_chain_bound",
  ``IS_NONE (transaction4_from_rlp (2 ** 64) 1 (typed_test_sign (LUPDATE (rlp_number (2 ** 64)) 0 typed_test_setcode)))``);

val () = typed_check ("typed_type4_max_chain",
  ``IS_SOME (transaction4_from_rlp (2 ** 64 - 1) 1 (typed_test_sign (LUPDATE (rlp_number (2 ** 64 - 1)) 0 typed_test_setcode)))``);

val () = typed_check ("typed_type4_nonce_bound",
  ``IS_NONE (transaction4_from_rlp 1 1 (typed_test_sign (LUPDATE (rlp_number (2 ** 64)) 1 typed_test_setcode)))``);

val () = typed_check ("typed_type4_max_nonce",
  ``IS_SOME (transaction4_from_rlp 1 1 (typed_test_sign (LUPDATE (rlp_number (2 ** 64 - 1)) 1 typed_test_setcode)))``);

val () = typed_check ("typed_blob_valid",
  ``IS_SOME (transaction3_from_rlp 1 1 (typed_test_sign typed_test_blob))``);

val () = typed_check ("typed_blob_hash_width",
  ``EVERY (λn. IS_NONE (transaction3_from_rlp 1 1 (typed_test_sign (LUPDATE (RLPL [RLPB (REPLICATE n 1w)]) 10 typed_test_blob)))) [0; 31; 33]``);

val () = typed_check ("typed_blob_fee_bound",
  ``IS_NONE (transaction3_from_rlp 1 1 (typed_test_sign (LUPDATE (rlp_number (2 ** 256)) 9 typed_test_blob)))``);

val () = typed_check ("typed_blob_fee_minimal",
  ``IS_NONE (transaction3_from_rlp 1 1 (typed_test_sign (LUPDATE (RLPB [0w; 1w]) 9 typed_test_blob)))``);

val () = typed_check ("typed_blob_fee_max",
  ``IS_SOME (transaction3_from_rlp 1 1 (typed_test_sign (LUPDATE (rlp_number (2 ** 256 - 1)) 9 typed_test_blob)))``);

val () = typed_check ("typed_authorization_minimal",
  ``EVERY (λi. IS_NONE (authorization_from_rlp (RLPL (LUPDATE (RLPB [0w; 1w]) i typed_test_auth)))) [0; 2; 3; 4; 5]``);

val () = typed_check ("typed_authorization_valid",
  ``IS_SOME (authorization_from_rlp (RLPL typed_test_auth))``);

val () = typed_check ("typed_authorization_semantic_skip",
  ``EVERY (λi. IS_SOME (authorization_from_rlp (RLPL (LUPDATE (rlp_number 0) i typed_test_auth)))) [4; 5]``);

val () = typed_check ("typed_authorization_u8_semantic_skip",
  ``IS_SOME (authorization_from_rlp (RLPL (LUPDATE (rlp_number 255) 3 typed_test_auth)))``);

val () = typed_check ("typed_withdrawal_max_u64",
  ``EVERY (λi. IS_SOME (withdrawal_from_rlp (RLPL (LUPDATE (rlp_number (2 ** 64 - 1)) i [rlp_number 0; rlp_number 0; RLPB (REPLICATE 20 0w); rlp_number 0])))) [0; 1; 3]``);

val () = typed_check ("typed_header_max_u64",
  ``EVERY (λi. IS_SOME (block_header_from_rlp (RLPL (LUPDATE (rlp_number (2 ** 64 - 1)) i typed_test_header)))) [17; 18]``);

val () = typed_check ("typed_header_max_timestamp",
  ``IS_SOME (block_header_from_rlp (RLPL (LUPDATE (rlp_number (2 ** 256 - 1)) 11 typed_test_header)))``);

val () = typed_check ("typed_signed_upfront_valid",
  ``case transaction_from_rlp 1 1 typed_test_valid of NONE => F | SOME tx =>
    IS_SOME (pre_transaction_updates
      (update_account 0x7e5f4552091a69125d5dfcb7b8c2659029395bdfw
        (empty_account_state with balance := 200000) empty_accounts) 1 tx)``);

val () = typed_check ("typed_signature_minimal_integers",
  ``case rlp_decode_chunks [DROP 1 (dest_RLPB typed_test_valid)] of
      NONE => F
    | SOME rlp => typed_test_signature_minimal_payload rlp``);

val () = typed_check ("typed_authorization_address_width",
  ``EVERY (λn. IS_NONE (authorization_from_rlp
    (RLPL (LUPDATE (RLPB (REPLICATE n 0w)) 1 typed_test_auth))))
    [0; 19; 21; 32]``);

val () = typed_check ("typed_authorization_u256_bounds",
  ``EVERY (λi. IS_NONE (authorization_from_rlp
    (RLPL (LUPDATE (rlp_number (2 ** 256)) i typed_test_auth))))
    [0; 4; 5]``);

val () = typed_check ("typed_authorization_u256_max",
  ``EVERY (λi. IS_SOME (authorization_from_rlp
    (RLPL (LUPDATE (rlp_number (2 ** 256 - 1)) i typed_test_auth))))
    [0; 4; 5]``);

val () = typed_check ("typed_authorization_nonce_bound",
  ``IS_NONE (authorization_from_rlp
    (RLPL (LUPDATE (rlp_number (2 ** 64)) 2 typed_test_auth)))``);

val () = typed_check ("typed_authorization_nonce_max",
  ``IS_SOME (authorization_from_rlp
    (RLPL (LUPDATE (rlp_number (2 ** 64 - 1)) 2 typed_test_auth)))``);

val () = typed_check ("typed_authorization_parity_bound",
  ``IS_NONE (authorization_from_rlp
    (RLPL (LUPDATE (rlp_number (2 ** 8)) 3 typed_test_auth)))``);

val () = typed_check ("typed_header_long_roots",
  ``EVERY (λi. IS_NONE (block_header_from_rlp
    (RLPL (LUPDATE (RLPB (REPLICATE 33 0w)) i typed_test_header))))
    [0; 1; 3; 4; 5; 13; 16; 19; 20]``);

val () = typed_check ("typed_header_long_address",
  ``IS_NONE (block_header_from_rlp
    (RLPL (LUPDATE (RLPB (REPLICATE 21 0w)) 2 typed_test_header)))``);

val () = typed_check ("typed_header_long_bloom",
  ``IS_NONE (block_header_from_rlp
    (RLPL (LUPDATE (RLPB (REPLICATE 257 0w)) 6 typed_test_header)))``);

val () = typed_check ("typed_header_nonce_width",
  ``EVERY (λn. IS_NONE (block_header_from_rlp
    (RLPL (LUPDATE (RLPB (REPLICATE n 0w)) 14 typed_test_header))))
    [0; 7; 9]``);

val () = if null (!typed_test_failures) then () else
  raise Fail ("typed decoder regressions: " ^
              Int.toString (length (!typed_test_failures)) ^ " failed");
