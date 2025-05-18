open HolKernel boolLib bossLib Parse dep_rewrite wordsLib
     wordsTheory listTheory rich_listTheory combinTheory
     numposrepTheory arithmeticTheory logrootTheory relationTheory
     vfmTypesTheory cv_transLib cv_stdTheory

val _ = new_theory "recursiveLengthPrefix";

(* TODO: move? *)

Theorem SUM_less_EVERY_less:
  SUM ls < n ==> EVERY (λx. x < n) ls
Proof
  Induct_on`ls` \\ rw[]
QED

(* -- *)

Datatype:
  rlp = RLPB (word8 list) | RLPL (rlp list)
End

Definition is_RLPL_def[simp]:
  (is_RLPL (RLPL _) = T) ∧
  (is_RLPL _ = F)
End

Definition is_RLPB_def[simp]:
  (is_RLPB (RLPB _) = T) ∧
  (is_RLPB _ = F)
End

Definition dest_RLPB_def[simp]:
  dest_RLPB (RLPB bs) = bs ∧
  dest_RLPB _ = []
End

Definition dest_RLPL_def[simp]:
  dest_RLPL (RLPL ls) = ls ∧
  dest_RLPL _ = []
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
  rlp_encode (RLPL rs) = rlp_encode_list_acc [] rs ∧
  rlp_encode_list_acc acc [] = rlp_list $ FLAT $ REVERSE acc ∧
  rlp_encode_list_acc acc (x::xs) =
  rlp_encode_list_acc (rlp_encode x :: acc) xs
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
  if prefix ≤ 0xb7 then
    if length > strLen then SOME (1, strLen, T) else NONE
  else
  let lenOfStrLen = prefix - 0xb7 in
  let strLen = num_of_be_bytes (TAKE lenOfStrLen (TL bs)) in
  if prefix ≤ 0xbf then
    if length > lenOfStrLen + strLen
    then SOME (1 + lenOfStrLen, strLen, T) else NONE
  else
  let listLen = prefix - 0xc0 in
  if prefix ≤ 0xf7 then
    if length > listLen then SOME (1, listLen, F) else NONE
  else
  let lenOfListLen = prefix - 0xf7 in
  let listLen = num_of_be_bytes (TAKE lenOfListLen (TL bs)) in
  if prefix ≤ 0xff then
    if length > lenOfListLen + listLen
    then SOME (1 + lenOfListLen, listLen, F)
    else NONE
  else NONE
End

val rlp_decode_length_pre_def = cv_auto_trans_pre rlp_decode_length_def;

Theorem rlp_decode_length_pre[cv_pre]:
  rlp_decode_length_pre bs
Proof
  rw[rlp_decode_length_pre_def]
QED

Theorem LENGTH_num_to_be_bytes:
  LENGTH (num_to_be_bytes n) =
  if n = 0 then 0 else SUC (LOG 256 n)
Proof
  rw[num_to_be_bytes_def, LENGTH_n2l]
QED

Theorem rlp_decode_length_RLPB:
  LENGTH bs < 2 ** 64 ⇒
  ∃offset.
    rlp_decode_length (rlp_encode (RLPB bs)) =
    SOME (offset, LENGTH bs, T) ∧
    LENGTH (rlp_encode (RLPB bs)) = offset + LENGTH bs ∧
    TAKE (LENGTH bs) (DROP offset (rlp_encode (RLPB bs))) = bs
Proof
  rw[rlp_encode_def]
  \\ rewrite_tac[rlp_bytes_def, rlp_decode_length_def]
  \\ IF_CASES_TAC >- rw[]
  \\ IF_CASES_TAC >- rw[]
  \\ qexists_tac`1 + 1 + LOG 256 (LENGTH bs)`
  \\ reverse conj_tac
  >- ( rw[DROP_APPEND, LENGTH_n2l, ADD1, TAKE_APPEND] \\ gvs[] )
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
  >- (
    gvs[Abbr`strLen'`, TAKE_APPEND, LENGTH_num_to_be_bytes]
    \\ Cases_on`bs = []` \\ gs[Abbr`length`] )
  \\ pop_assum mp_tac
  \\ qpat_x_assum`_ = LENGTH _`(assume_tac o SYM)
  \\ gvs[TAKE_APPEND, Abbr`strLen'`]
  \\ gvs[Abbr`length`]
  \\ Cases_on`LOG 256 (LENGTH bs) ≤ 7` >- gs[]
  \\ `LOG 256 (LENGTH bs) = 8` by gs[] \\ gvs[]
  \\ qspecl_then[`256`,`LENGTH bs`,`2 ** 64 - 1`]mp_tac LOG_LE_MONO
  \\ simp[Abbr`lenOfListLen`]
QED

Theorem LENGTH_rlp_list:
  LENGTH (rlp_list bs) =
  1 + LENGTH bs +
  if LENGTH bs < 56 then 0
  else 1 + LOG 256 (LENGTH bs)
Proof
  rw[rlp_list_def, ADD1, LENGTH_n2l] \\ gs[]
QED

Theorem rlp_decode_length_offset_zero:
  rlp_decode_length bs = SOME (0,l,b) ==>
  ((l = 1) ∧ (b = T))
Proof
  rewrite_tac[rlp_decode_length_def]
  \\ BasicProvers.LET_ELIM_TAC
  \\ rpt (pop_assum mp_tac)
  \\ rw[]
QED

Theorem rlp_decode_length_length_less_eq:
  rlp_decode_length bs = SOME (off, len, b) ==>
  off + len ≤ LENGTH bs
Proof
  rewrite_tac[rlp_decode_length_def]
  \\ BasicProvers.LET_ELIM_TAC
  \\ qpat_x_assum`_ = _`mp_tac
  \\ rw[]
QED

Theorem rlp_decode_length_nil[simp]:
  rlp_decode_length [] = NONE
Proof
  rw[rlp_decode_length_def]
QED

Definition rlp_decode_list_def:
  rlp_decode_list bs =
    case rlp_decode_length bs
      of NONE => []
       | SOME (offset, dataLen, isBS) =>
           let bs = DROP offset bs in
           let data = TAKE dataLen bs in
           let bs = DROP dataLen bs in
           let rlp = if isBS then RLPB data
                     else RLPL $ rlp_decode_list data in
           rlp :: rlp_decode_list bs
Termination
  WF_REL_TAC ‘measure LENGTH’
  \\ rw[] \\ CCONTR_TAC \\ gvs[]
  \\ TRY $ drule rlp_decode_length_offset_zero \\ rw[]
  \\ pop_assum mp_tac
  \\ rw[LENGTH_TAKE_EQ]
  \\ gvs[NOT_LESS_EQUAL]
  \\ CCONTR_TAC \\ gvs[NOT_LESS]
  \\ TRY $ drule rlp_decode_length_offset_zero \\ rw[]
  \\ drule rlp_decode_length_length_less_eq
  \\ strip_tac \\ gvs[]
  \\ qmatch_asmsub_rename_tac`SOME (off,len,_)`
  \\ `off + len ≤ len` by gs[]
  \\ Cases_on`off = 0` \\ gs[]
  \\ drule rlp_decode_length_offset_zero
  \\ rw[]
End

Definition rlp_decode_list_tr_def:
  rlp_decode_list_tr bs ls stk =
  case rlp_decode_length bs
    of NONE => (
      case stk
        of [] => REVERSE ls
         | ((pbs,pls)::stk) =>
             rlp_decode_list_tr pbs ((RLPL (REVERSE ls))::pls) stk)
     | SOME (offset, dataLen, isBS) =>
       let bs = DROP offset bs in
       let data = TAKE dataLen bs in
       let bs = DROP dataLen bs in
       if isBS then
         rlp_decode_list_tr bs ((RLPB data)::ls) stk
       else
         rlp_decode_list_tr data [] ((bs,ls)::stk)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λ(bs,ls,stk).
    (LENGTH bs + SUM (MAP (LENGTH o FST) stk),
     LENGTH stk))’
  \\ rw[]
  \\ drule rlp_decode_length_length_less_eq
  \\ rw[]
  \\ CCONTR_TAC \\ gvs[]
  \\ drule rlp_decode_length_offset_zero
  \\ rw[]
End

val () = cv_auto_trans rlp_decode_list_tr_def;

Definition unwind_stk_def:
  unwind_stk [] = [] ∧
  unwind_stk ((bs,ls)::[]) =
    REVERSE ls ++ rlp_decode_list bs ∧
  unwind_stk ((bs,ls)::(pbs,pls)::stk) =
    unwind_stk ((pbs,(RLPL (REVERSE ls ++ rlp_decode_list bs))::pls)::stk)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<)
    (λx. (SUM (MAP (LENGTH o FST) x), LENGTH x))’
  \\ rw[]
End

Theorem rlp_decode_list_tr_unwind_stk:
  ∀bs ls stk.
    rlp_decode_list_tr bs ls stk =
    unwind_stk ((bs,ls)::stk)
Proof
  ho_match_mp_tac rlp_decode_list_tr_ind
  \\ rw[]
  \\ rw[Once rlp_decode_list_tr_def]
  \\ Cases_on`rlp_decode_length bs` \\ gvs[]
  >- (
    CASE_TAC
    >- (
      rw[Once unwind_stk_def]
      \\ rw[Once rlp_decode_list_def] )
    \\ CASE_TAC \\ gvs[]
    \\ rw[Once unwind_stk_def, SimpRHS]
    \\ rw[Once rlp_decode_list_def] )
  \\ CASE_TAC
  \\ CASE_TAC
  \\ gvs[]
  \\ rw[] \\ gvs[]
  >- (
    simp[Once $ oneline unwind_stk_def]
    \\ CASE_TAC
    >- (
      simp[unwind_stk_def]
      \\ simp[Once rlp_decode_list_def, SimpRHS] )
    \\ CASE_TAC \\ gvs[]
    \\ simp[Once unwind_stk_def, SimpRHS]
    \\ simp[Once rlp_decode_list_def, SimpRHS] )
  \\ simp[Once $ oneline unwind_stk_def]
  \\ simp[Once $ oneline unwind_stk_def, SimpRHS]
  \\ CASE_TAC
  >- (
    simp[Once rlp_decode_list_def, SimpRHS]
    \\ simp[unwind_stk_def] )
  \\ CASE_TAC
  \\ simp[Once rlp_decode_list_def, SimpRHS]
  \\ simp[Once unwind_stk_def]
QED

Theorem rlp_decode_list_eq_tr:
  rlp_decode_list bs =
  rlp_decode_list_tr bs [] []
Proof
  rw[rlp_decode_list_tr_unwind_stk, unwind_stk_def]
QED

Definition rlp_decode_def:
  rlp_decode bs =
  case rlp_decode_list bs of
     | [rlp] => SOME rlp
     | _ => NONE
End

val () = rlp_decode_def
  |> SRULE [rlp_decode_list_eq_tr]
  |> cv_auto_trans;

Theorem rlp_encode_list_map:
  ∀ls acc. rlp_encode_list_acc acc ls =
  rlp_list (FLAT (REVERSE (REVERSE (MAP rlp_encode ls) ++ acc)))
Proof
  Induct \\ rw[rlp_encode_def]
QED

Theorem rlp_decode_length_append:
  rlp_decode_length b1 = SOME p ⇒
  rlp_decode_length (b1 ++ b2) = SOME p
Proof
  rewrite_tac[rlp_decode_length_def]
  \\ BasicProvers.LET_ELIM_TAC
  \\ gvs[Abbr`length'`]
  \\ Cases_on`b1` \\ gvs[Abbr`prefix`, Abbr`prefix'`]
  \\ IF_CASES_TAC \\ gvs[]
  \\ qpat_x_assum`_ = SOME _`mp_tac
  \\ IF_CASES_TAC >> gvs[]
  \\ IF_CASES_TAC
  >- (
    gvs[]
    \\ strip_tac
    \\ gvs[TAKE_APPEND]
    \\ Cases_on`lenOfStrLen ≤ LENGTH t`
    >- (
      `lenOfStrLen - LENGTH t = 0` by gs[]
      \\ pop_assum SUBST_ALL_TAC \\ gvs[] )
    \\ gvs[NOT_LESS_EQUAL, TAKE_LENGTH_TOO_LONG]
    \\ `length ≤ lenOfStrLen` by simp[Abbr`length`]
    \\ qpat_x_assum`length ≤ _`mp_tac
    \\ qpat_x_assum`length > _`mp_tac
    \\ simp[] )
  \\ IF_CASES_TAC >- gvs[]
  \\ IF_CASES_TAC >- (
    gvs[]
    \\ strip_tac \\ gvs[TAKE_APPEND]
    \\ Cases_on`lenOfListLen ≤ LENGTH t`
    >- (
      `lenOfListLen - LENGTH t = 0` by gs[]
      \\ pop_assum SUBST_ALL_TAC \\ gvs[])
    \\ gvs[NOT_LESS_EQUAL, TAKE_LENGTH_TOO_LONG]
    \\ `length ≤ lenOfListLen` by simp[Abbr`length`]
    \\ qpat_x_assum`length ≤ _`mp_tac
    \\ qpat_x_assum`length > _`mp_tac
    \\ simp[] )
  \\ gs[]
QED

Theorem rlp_decode_length_list:
  LENGTH bs < 2 ** 64 ⇒
  ∃offset.
  rlp_decode_length (rlp_list bs) =
    SOME (offset, LENGTH bs, F) ∧
  offset + LENGTH bs = LENGTH $ rlp_list bs ∧
  rlp_list bs = TAKE offset (rlp_list bs) ++ bs
Proof
  rw[rlp_list_def]
  >- rw[rlp_decode_length_def]
  \\ rewrite_tac[rlp_decode_length_def]
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`prefix ≤ _`
  \\ pop_assum mp_tac
  \\ simp[LENGTH_n2l]
  \\ Cases_on`bs = []` \\ gs[]
  \\ `LOG 256 (LENGTH bs) ≤ 8`
  by ( irule EXP_TO_LOG \\ gs[] )
  \\ Cases_on`LOG 256 (LENGTH bs) = 8`
  >- (
    qspecl_then[`256`,`LENGTH bs`,`2 ** 64 - 1`]mp_tac LOG_LE_MONO
    \\ gvs[] )
  \\ simp[]
  \\ strip_tac
  \\ gvs[Abbr`prefix`]
  \\ simp[TAKE_APPEND, LENGTH_n2l, TAKE_LENGTH_TOO_LONG]
  \\ qmatch_goalsub_abbrev_tac`num_of_be_bytes bb`
  \\ `bb = num_to_be_bytes (LENGTH bs)`
  by ( simp[num_to_be_bytes_def, Abbr`bb`, MAP_REVERSE] )
  \\ simp[DROP_APPEND, LENGTH_num_to_be_bytes]
QED

Theorem rlp_decode_list_encode:
  ∀ls xs. ls = FLAT (MAP rlp_encode xs) ∧
  EVERY (λx. LENGTH (rlp_encode x) < 2 ** 64) xs
  ⇒
  rlp_decode_list ls = xs
Proof
  ho_match_mp_tac rlp_decode_list_ind
  \\ rw[]
  \\ rw[Once rlp_decode_list_def]
  \\ Cases_on`xs` \\ gvs[]
  \\ qmatch_goalsub_rename_tac`rlp_encode x`
  \\ Cases_on`x`
  >- (
    qmatch_asmsub_rename_tac`RLPB bs`
    \\ `LENGTH bs < 2 ** 64`
    by (
      fs[rlp_encode_def, rlp_bytes_def]
      \\ qpat_x_assum`LENGTH _ < _`mp_tac \\ rw[] )
    \\ drule rlp_decode_length_RLPB
    \\ rw[]
    \\ qmatch_goalsub_abbrev_tac`_ ++ ws`
    \\ drule_then(qspec_then`ws`mp_tac) rlp_decode_length_append
    \\ rw[DROP_DROP, DROP_APPEND, DROP_LENGTH_TOO_LONG, iffRL SUB_EQ_0]
    \\ rw[TAKE_APPEND, Abbr`ws`]
    \\ last_x_assum irule
    \\ gs[DROP_APPEND, DROP_DROP, iffRL SUB_EQ_0])
  \\ qmatch_asmsub_rename_tac`RLPL ls`
  \\ qmatch_goalsub_abbrev_tac`_ ++ ws`
  \\ gs[rlp_encode_def, rlp_encode_list_map]
  \\ qmatch_goalsub_abbrev_tac`rlp_list bs`
  \\ `LENGTH bs < 2 ** 64`
  by ( simp[Abbr`bs`] \\ gs[LENGTH_rlp_list] )
  \\ drule rlp_decode_length_list
  \\ strip_tac
  \\ drule_then(qspec_then`ws`mp_tac) rlp_decode_length_append
  \\ drule rlp_decode_length_length_less_eq
  \\ strip_tac
  \\ rw[DROP_APPEND, DROP_DROP, TAKE_APPEND, iffRL SUB_EQ_0]
  \\ gvs[DROP_APPEND, iffRL SUB_EQ_0, TAKE_APPEND]
  >- (
    qmatch_asmsub_abbrev_tac`rlp_list bs = off ++ bs`
    \\ simp[DROP_APPEND]
    \\ gvs[DROP_LENGTH_TOO_LONG, iffRL SUB_EQ_0, TAKE_APPEND]
    \\ `LENGTH off = offset`
    by (
      rw[Abbr`off`, LENGTH_TAKE_EQ]
      \\ gvs[LENGTH_TAKE_EQ] )
    \\ simp[DROP_LENGTH_TOO_LONG]
    \\ qunabbrev_tac`bs`
    \\ first_x_assum irule
    \\ gs[LENGTH_rlp_list, LENGTH_FLAT, DROP_APPEND]
    \\ gs[MAP_MAP_o, o_DEF]
    \\ qmatch_asmsub_abbrev_tac`SUM lf`
    \\ `SUM lf < 2 ** 64` by simp[]
    \\ drule SUM_less_EVERY_less
    \\ simp[Abbr`lf`, EVERY_MAP]
    \\ simp[TAKE_APPEND, DROP_LENGTH_TOO_LONG, LENGTH_FLAT, MAP_MAP_o, o_DEF])
  \\ qmatch_asmsub_abbrev_tac`rlp_list bs = off ++ bs`
  \\ simp[DROP_APPEND]
  \\ gvs[DROP_LENGTH_TOO_LONG, iffRL SUB_EQ_0, TAKE_APPEND]
  \\ `LENGTH off = offset`
  by (
    rw[Abbr`off`, LENGTH_TAKE_EQ]
    \\ gvs[LENGTH_TAKE_EQ] )
  \\ simp[DROP_LENGTH_TOO_LONG]
  \\ qunabbrev_tac`ws`
  \\ last_x_assum irule
  \\ simp[DROP_APPEND, TAKE_APPEND, DROP_LENGTH_TOO_LONG]
QED

Theorem rlp_decode_encode:
  LENGTH (rlp_encode x) ≤ 2 ** 64 (* TODO: this bound could be looser *)
  ⇒ rlp_decode (rlp_encode x) = SOME x
Proof
  Cases_on`x`
  \\ rw[rlp_encode_def, rlp_encode_list_map]
  >- (
    rw[rlp_decode_def]
    \\ rw[Once rlp_decode_list_def]
    \\ qmatch_goalsub_rename_tac`rlp_decode_length (rlp_bytes bs)`
    \\ `rlp_bytes bs = rlp_encode (RLPB bs)` by rw[rlp_encode_def]
    \\ pop_assum SUBST1_TAC
    \\ `LENGTH bs < 2 ** 64`
    by ( fs[rlp_bytes_def] \\ pop_assum mp_tac \\ rw[] )
    \\ drule rlp_decode_length_RLPB
    \\ strip_tac
    \\ simp[DROP_DROP, DROP_LENGTH_TOO_LONG]
    \\ rw[Once rlp_decode_list_def] )
  \\ rw[rlp_encode_def, rlp_encode_list_map]
  \\ qmatch_goalsub_abbrev_tac`rlp_list bs`
  \\ rw[rlp_decode_def]
  \\ rw[Once rlp_decode_list_def]
  \\ `LENGTH bs < 2 ** 64` by fs[LENGTH_rlp_list]
  \\ drule rlp_decode_length_list
  \\ rw[] \\ rw[DROP_DROP]
  \\ rw[Once rlp_decode_list_def]
  \\ qmatch_asmsub_abbrev_tac`off ++ bs`
  \\ `LENGTH off = offset` by simp[Abbr`off`]
  \\ simp[DROP_APPEND]
  \\ `DROP offset off = []` by metis_tac[DROP_LENGTH_NIL]
  \\ rw[]
  \\ irule rlp_decode_list_encode
  \\ rw[]
  \\ gvs[LENGTH_rlp_list, Abbr`bs`, LENGTH_FLAT]
  \\ qmatch_asmsub_abbrev_tac`SUM lf`
  \\ `SUM lf < 2 ** 64` by simp[]
  \\ drule SUM_less_EVERY_less
  \\ simp[Abbr`lf`, EVERY_MAP]
QED

val _ = export_theory();
