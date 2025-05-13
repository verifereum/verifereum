open HolKernel boolLib bossLib Parse dep_rewrite
     wordsLib wordsTheory listTheory rich_listTheory combinTheory
     numposrepTheory arithmeticTheory logrootTheory
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

Definition num_of_be_bytes_def:
  num_of_be_bytes bs =
  l2n 256 $ MAP w2n $ REVERSE bs
End

Theorem num_of_to_be_bytes[simp]:
  num_of_be_bytes (num_to_be_bytes n) = n
Proof
  rw[num_of_be_bytes_def, num_to_be_bytes_def, MAP_MAP_o, o_DEF]
  \\ qmatch_goalsub_abbrev_tac`MAP f ls`
  \\ `MAP f ls = MAP I ls`
  by (
    rw[MAP_EQ_f, Abbr`ls`, Abbr`f`]
    \\ qspec_then`256` mp_tac n2l_BOUND
    \\ rw[EVERY_MEM]
    \\ first_x_assum drule \\ rw[] )
  \\ fs[Abbr`ls`]
  \\ irule l2n_n2l
  \\ rw[]
QED

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

Definition rlp_decode_length_def:
  rlp_decode_length bs =
  let length = LENGTH bs in
  if length = 0 then NONE else
  let prefix = w2n (EL 0 bs) in
  if prefix ≤ 0x7f
  then SOME (0, 1, T) else
  let strLen = prefix - 0x80 in
  if prefix ≤ 0xb7 ∧ length > strLen
  then SOME (1, strLen, T) else
  let lenOfStrLen = prefix - 0xb7 in
  let strLen = num_of_be_bytes (TAKE lenOfStrLen (TL bs)) in
  if prefix ≤ 0xbf ∧ length > lenOfStrLen + strLen
  then SOME (1 + lenOfStrLen, strLen, T) else
  let listLen = prefix - 0xc0 in
  if prefix ≤ 0xf7 ∧ length > listLen
  then SOME (1, listLen, F) else
  let lenOfListLen = prefix - 0xf7 in
  let listLen = num_of_be_bytes (TAKE lenOfListLen (TL bs)) in
  if prefix ≤ 0xff ∧ length > lenOfListLen + listLen
  then SOME (1 + lenOfListLen, listLen, F)
  else NONE
End

Theorem rlp_decode_length_RLPB:
  LENGTH bs < 2 ** 64 ⇒
  ∃offset.
    rlp_decode_length (rlp_encode (RLPB bs)) =
    SOME (offset, LENGTH bs, T) ∧
    TAKE (LENGTH bs) (DROP offset (rlp_encode (RLPB bs))) = bs
Proof
  rw[rlp_encode_def]
  \\ rewrite_tac[rlp_bytes_def, rlp_decode_length_def]
  \\ IF_CASES_TAC >- rw[]
  \\ IF_CASES_TAC >- rw[]
  \\ qexists_tac`1 + 1 + LOG 256 (LENGTH bs)`
  \\ reverse conj_tac
  >- rw[DROP_APPEND, LENGTH_n2l, ADD1, TAKE_APPEND]
  \\ BasicProvers.LET_ELIM_TAC
  \\ IF_CASES_TAC >- gvs[Abbr`length`]
  \\ gvs[]
  \\ `LENGTH lengthBytes = 1 + LOG 256 (LENGTH bs)`
  by ( rw[Abbr`lengthBytes`, LENGTH_n2l] \\ gvs[] )
  \\ gvs[]
  \\ `LOG 256 (LENGTH bs) ≤ 8`
  by ( irule EXP_TO_LOG \\ gs[] )
  \\ `prefix = LOG 256 (LENGTH bs) + 184`
  by simp[Abbr`prefix`]
  \\ gvs[Abbr`prefix`]
  \\ `lengthBytes = num_to_be_bytes $ LENGTH bs`
  by (
    simp[Abbr`lengthBytes`, num_to_be_bytes_def]
    \\ IF_CASES_TAC \\ gvs[MAP_REVERSE] )
  \\ IF_CASES_TAC
  >- gvs[Abbr`strLen'`, TAKE_APPEND]
  \\ pop_assum mp_tac
  \\ qpat_x_assum`_ = LENGTH _`(assume_tac o SYM)
  \\ gvs[TAKE_APPEND, Abbr`strLen'`]
  \\ gvs[Abbr`length`]
  \\ Cases_on`LOG 256 (LENGTH bs) ≤ 7` >- gs[]
  \\ `LOG 256 (LENGTH bs) = 8` by gs[] \\ gvs[]
  \\ qspecl_then[`256`,`LENGTH bs`,`2 ** 64 - 1`]mp_tac LOG_LE_MONO
  \\ simp[Abbr`lenOfListLen`]
QED

val _ = export_theory();
