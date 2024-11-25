open HolKernel boolLib bossLib Parse
     wordsLib wordsTheory listTheory
     cv_transLib cv_stdTheory

val _ = new_theory "recursiveLengthPrefix";

Definition rlp_bytes_def:
  rlp_bytes (bytes : word8 list) =
  if LENGTH bytes = 1 ∧ w2n (HD bytes) < 128 then bytes
  else if LENGTH bytes < 56 then n2w (128 + LENGTH bytes) :: bytes
  else
    let lengthBytes = MAP n2w $ REVERSE $ n2l 256 $ LENGTH bytes
  in
    [n2w (183 + LENGTH lengthBytes)] ++ lengthBytes ++ bytes
End

Definition rlp_list_def:
  rlp_list (payload : word8 list) =
  if LENGTH payload < 0x38 then n2w (0xc0 + LENGTH payload) :: payload
  else
    let lengthBytes = MAP n2w $ REVERSE $ n2l 256 $ LENGTH payload
  in
    [n2w (0xf7 + LENGTH lengthBytes)] ++ lengthBytes ++ payload
End

val () = cv_auto_trans numposrepTheory.n2l_n2lA;

val rlp_bytes_alt =
  rlp_bytes_def |> ONCE_REWRITE_RULE[
    METIS_PROVE[]“A ∧ B ⇔ (if A then B else F)”
  ];

val rlp_bytes_pre_def = cv_auto_trans_pre rlp_bytes_alt;

Theorem rlp_bytes_pre[cv_pre]:
  ∀b. rlp_bytes_pre b
Proof
  rw[rlp_bytes_pre_def, LENGTH_EQ_NUM_compute]
QED

val _ = export_theory();
