Theory vfmTypes
Ancestors
  arithmetic byte cv_std divides list rich_list combin numposrep words
  keccak
Libs
  blastLib
  cv_transLib

val _ = tight_equality();

Theorem option_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="option",Tyop="option"}));

Theorem prod_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="pair",Tyop="prod"}));

Theorem sum_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="sum",Tyop="sum"}));

val () = cv_trans (word_of_bytes_le_eq_num_of_bytes |> INST_TYPE [alpha |-> “:160”] |> SRULE[compute_divides]);
val () = cv_trans (word_of_bytes_be_eq_num_of_bytes |> INST_TYPE [alpha |-> “:160”] |> SRULE[compute_divides]);
val () = cv_trans (word_of_bytes_le_eq_num_of_bytes |> INST_TYPE [alpha |-> “:256”] |> SRULE[compute_divides]);
val () = cv_trans (word_of_bytes_be_eq_num_of_bytes |> INST_TYPE [alpha |-> “:256”] |> SRULE[compute_divides]);
val () = cv_trans (word_of_bytes_le_eq_num_of_bytes |> INST_TYPE [alpha |-> “:64”] |> SRULE[compute_divides]);
val () = cv_trans (word_of_bytes_be_eq_num_of_bytes |> INST_TYPE [alpha |-> “:64”] |> SRULE[compute_divides]);
val () = cv_trans (word_to_bytes_le_eq_bytes_of_num |> INST_TYPE [alpha |-> “:256”]);
val () = cv_trans (word_to_bytes_be_eq_bytes_of_num |> INST_TYPE [alpha |-> “:256”]);
val () = cv_trans (word_to_bytes_le_eq_bytes_of_num |> INST_TYPE [alpha |-> “:64”]);
val () = cv_trans (word_to_bytes_be_eq_bytes_of_num |> INST_TYPE [alpha |-> “:64”]);

val vars = List.tabulate(32, fn n => mk_var("w" ^ Int.toString n, “:256 word”))

Theorem word_to_bytes_word_of_bytes_256[simp]:
  word_of_bytes be (0w:256 word) (word_to_bytes w be) = w
Proof
  rw[word_to_bytes_def, word_to_bytes_aux_compute]
  \\ rw[word_of_bytes_def]
  \\ map_every (fn wn =>
    qmatch_goalsub_abbrev_tac`set_byte _ _ ^wn`
    \\ simp[set_byte_get_byte_copy, byte_index_def]
    \\ pop_assum mp_tac) vars
  \\ rpt strip_tac
  \\ Cases_on`be` \\ gvs[]
  \\ map_every (fn v => BBLAST_TAC \\ qunabbrev_tac[ANTIQUOTE v]) vars
  \\ rw[]
QED

val () = cv_auto_trans numposrepTheory.n2l_n2lA;

Type address = “:160 word”
Type bytes32 = “:256 word”
Type byte = “:word8”
Datatype:
  event =
  <| logger : address
   ; topics : bytes32 list
   ; data : byte list
   |>
End

Definition num_to_be_bytes_def:
  num_to_be_bytes n : word8 list =
  if n = 0 then [] else REVERSE $ MAP n2w $ n2l 256 n
End

val () = cv_auto_trans num_to_be_bytes_def;

Definition num_of_be_bytes_def:
  num_of_be_bytes bs =
  l2n 256 $ MAP w2n $ REVERSE bs
End

val () = cv_auto_trans num_of_be_bytes_def;

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

Definition take_pad_0_def:
  take_pad_0 z l = PAD_RIGHT 0w z (TAKE z l)
End

Theorem take_pad_0_0[simp]:
  take_pad_0 0 l = []
Proof
  rw[take_pad_0_def, PAD_RIGHT]
QED

Theorem LENGTH_take_pad_0[simp]:
  LENGTH (take_pad_0 z l) = z
Proof
  rw[take_pad_0_def, bitstringTheory.length_pad_right, LENGTH_TAKE_EQ]
QED

Theorem take_pad_0_IS_PREFIX:
  ∃m. take_pad_0 n t ≼ t ++ REPLICATE m 0w
Proof
  rw[take_pad_0_def, PAD_RIGHT, IS_PREFIX_APPEND]
  \\ `t = TAKE n t ++ DROP n t` by simp[]
  \\ pop_assum(fn th => CONV_TAC(STRIP_QUANT_CONV(LAND_CONV(ONCE_REWRITE_CONV[th]))))
  \\ simp[REPLICATE_GENLIST, LENGTH_TAKE_EQ]
  \\ rw[DROP_LENGTH_TOO_LONG]
  \\ qexists_tac`n - LENGTH t` \\ rw[]
QED

Theorem PAD_RIGHT_CONS:
  PAD_RIGHT x y (h::t) = h::PAD_RIGHT x (PRE y) t
Proof
  rw[PAD_RIGHT] \\ Cases_on`y` \\ gs[]
QED

(* alternative characterisation *)
Theorem take_pad_0_pad_take:
  take_pad_0 z l = TAKE z (PAD_RIGHT 0w z l)
Proof
  rw[take_pad_0_def]
  \\ qid_spec_tac`z`
  \\ Induct_on`l`
  \\ gs[bitstringTheory.length_pad_right]
  \\ rw[Once TAKE_def]
  >- EVAL_TAC
  \\ gs[PAD_RIGHT_CONS, PRE_SUB1]
QED
