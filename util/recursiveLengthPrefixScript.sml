open HolKernel boolLib bossLib Parse
     wordsLib wordsTheory listTheory
     vfmTypesTheory cv_transLib cv_stdTheory

val _ = new_theory "recursiveLengthPrefix";

Datatype:
  rlp = RLPB (word8 list) | RLPL (rlp list)
End

Definition dest_RLPB_def:
  dest_RLPB (RLPB bs) = bs ∧
  dest_RLPB _ = []
End

Definition num_to_be_bytes_def:
  num_to_be_bytes n : word8 list =
  if n = 0 then [] else REVERSE $ MAP n2w $ n2l 256 n
End

Definition rlp_number_def:
  rlp_number n = RLPB $ num_to_be_bytes n
End

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

Definition rlp_encode_def:
  rlp_encode (RLPB bs) = rlp_bytes bs ∧
  rlp_encode (RLPL rs) = rlp_encode_list [] rs ∧
  rlp_encode_list acc [] = rlp_list $ FLAT $ REVERSE acc ∧
  rlp_encode_list acc (x::xs) =
  rlp_encode_list (rlp_encode x :: acc) xs
End

val () = cv_auto_trans rlp_encode_def;

val _ = export_theory();
