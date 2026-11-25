Theory recursiveLengthPrefixCanonical
Ancestors recursiveLengthPrefix
Libs wordsLib cv_transLib

(* Prefix canonicality is independent of transaction integer-field rules:
   the byte 00 is canonical RLP even though it is not a minimal integer. *)
Definition rlp_canonical_prefix_case_def:
  rlp_canonical_prefix_case (bs : word8 list) =
    (rlp_decode_length bs = NONE /\
     rlp_decode bs = NONE /\
     EVERY (\css.
       rlp_decode_length_chunks (LENGTH bs) css = NONE /\
       rlp_decode_chunks css = NONE)
       [[bs]; MAP (\b. [b]) bs; [] :: MAP (\b. [b]) bs ++ [[]]])
End
val () = cv_auto_trans rlp_canonical_prefix_case_def;

Definition rlp_noncanonical_prefixes_def:
  rlp_noncanonical_prefixes : word8 list list =
    [[0x81w; 0x00w]; [0x81w; 0x7fw];
     [0xb8w; 0x00w]; [0xb8w; 0x01w; 0x80w];
     [0xb8w; 0x37w] ++ REPLICATE 55 0w;
     [0xb9w; 0x00w; 0x38w] ++ REPLICATE 56 0w;
     [0xf8w; 0x00w]; [0xf8w; 0x01w; 0x80w];
     [0xf8w; 0x37w] ++ REPLICATE 55 0x80w;
     [0xf9w; 0x00w; 0x38w] ++ REPLICATE 56 0x80w]
End
val () = cv_auto_trans rlp_noncanonical_prefixes_def;

(* Evaluate every case before reporting failures, so the pre-fix run records
   both string and list failures rather than stopping at the first one. *)
Definition rlp_prefix_results_def:
  rlp_prefix_results = MAP rlp_canonical_prefix_case rlp_noncanonical_prefixes
End
val () = cv_auto_trans rlp_prefix_results_def;
val prefix_results = cv_eval ``rlp_prefix_results``;
val () = print ("RLP canonical-prefix results: " ^
                term_to_string (rhs (concl prefix_results)) ^ "\n");

Definition rlp_enclosing_results_def:
  rlp_enclosing_results =
    MAP (\bs. rlp_decode bs = NONE /\
              rlp_decode_chunks (MAP (\b. [b]) bs) = NONE)
    [[0xc2w; 0x81w; 0x00w]; [0xc2w; 0xb8w; 0x00w];
     [0xc2w; 0xf8w; 0x00w]; [0x80w; 0x81w; 0x00w];
     [0xc1w; 0xb8w]; [0x80w; 0xb8w]]
End
val () = cv_auto_trans rlp_enclosing_results_def;
val enclosing_results = cv_eval ``rlp_enclosing_results``;
val () = print ("RLP malformed-enclosing results: " ^
                term_to_string (rhs (concl enclosing_results)) ^ "\n");

Definition rlp_canonical_controls_def:
  rlp_canonical_controls =
  EVERY (\r.
    rlp_decode (rlp_encode r) = SOME r /\
    rlp_decode_chunks (MAP (\b. [b]) (rlp_encode r)) = SOME r)
    [RLPB []; RLPB [0w]; RLPB [0x7fw]; RLPB [0x80w];
     RLPB (REPLICATE 55 0w); RLPB (REPLICATE 56 0w);
     RLPB (REPLICATE 256 0w); RLPL [];
     RLPL (REPLICATE 55 (RLPB []));
     RLPL (REPLICATE 56 (RLPB []));
     RLPL (REPLICATE 256 (RLPB []))]
End
val () = cv_auto_trans rlp_canonical_controls_def;

Theorem rlp_canonical_controls_pass:
  rlp_canonical_controls
Proof
  CONV_TAC cv_eval
QED

Theorem rlp_noncanonical_prefixes_rejected:
  EVERY I rlp_prefix_results
Proof
  simp[prefix_results]
QED

Theorem rlp_malformed_enclosing_rejected:
  EVERY I rlp_enclosing_results
Proof
  simp[enclosing_results]
QED
