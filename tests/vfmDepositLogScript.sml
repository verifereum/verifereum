Theory vfmDepositLog
Ancestors byte vfmCompute
Libs cv_transLib wordsLib

(* Deposit-log data must have exactly the fixed DepositEvent layout. *)
Definition deposit_test_word_def:
  deposit_test_word n = word_to_bytes (n2w n : bytes32) T
End
val () = cv_auto_trans $ REWRITE_RULE [GSYM word_to_bytes_be_def]
  deposit_test_word_def;

Definition deposit_test_log_def:
  deposit_test_log =
    deposit_test_word 160 ++ deposit_test_word 256 ++
    deposit_test_word 320 ++ deposit_test_word 384 ++
    deposit_test_word 512 ++
    deposit_test_word 48 ++ REPLICATE 48 1w ++ REPLICATE 16 0w ++
    deposit_test_word 32 ++ REPLICATE 32 2w ++
    deposit_test_word 8 ++ REPLICATE 8 3w ++ REPLICATE 24 0w ++
    deposit_test_word 96 ++ REPLICATE 96 4w ++
    deposit_test_word 8 ++ REPLICATE 8 5w ++ REPLICATE 24 (0w:byte)
End
val () = cv_auto_trans deposit_test_log_def;

Theorem deposit_log_well_formed:
  parse_deposit_request deposit_test_log =
    SOME (REPLICATE 48 1w ++ REPLICATE 32 2w ++ REPLICATE 8 3w ++
          REPLICATE 96 4w ++ REPLICATE 8 5w)
Proof
  CONV_TAC cv_eval
QED

Theorem deposit_log_wrong_offset:
  parse_deposit_request (deposit_test_word 161 ++ DROP 32 deposit_test_log) =
    NONE
Proof
  CONV_TAC cv_eval
QED

Theorem deposit_log_too_long:
  parse_deposit_request (deposit_test_log ++ [0w]) = NONE
Proof
  CONV_TAC cv_eval
QED
