open HolKernel boolLib bossLib Parse wordsLib dep_rewrite blastLib
     listTheory rich_listTheory arithmeticTheory bitTheory
     numposrepTheory byteTheory wordsTheory dividesTheory
     integerTheory integer_wordTheory vfmTypesTheory
     cvTheory cv_stdTheory cv_transLib

val () = new_theory "contractABI";

val () = numLib.prefer_num();

(* TODO: move *)

val vars = List.tabulate(32, fn n => mk_var("w" ^ Int.toString n, “:bytes32”))

Theorem word_to_bytes_word_of_bytes_256[simp]:
  word_of_bytes be (0w:bytes32) (word_to_bytes w be) = w
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

Theorem c2n_cv_add[simp]:
  cv$c2n (cv_add v1 v2) = cv$c2n v1 + cv$c2n v2
Proof
  Cases_on`v1` \\ Cases_on`v2` \\ rw[]
QED

Theorem c2n_cv_mul[simp]:
  cv$c2n (cv_mul v1 v2) = cv$c2n v1 * cv$c2n v2
Proof
  Cases_on`v1` \\ Cases_on`v2` \\ rw[]
QED

Theorem cv_lt_Num_0:
  (cv$c2b $ cv_lt (Num 0) x) = ∃n. x = Num (SUC n)
Proof
  Cases_on`x` \\ rw[cv_lt_def]
  \\ Cases_on`m` \\ simp[]
QED

Theorem LENGTH_word_to_bytes_aux[simp]:
  LENGTH (word_to_bytes_aux n w b) = n
Proof
  Induct_on`n` \\ rw[word_to_bytes_aux_def]
QED

Theorem LENGTH_word_to_bytes[simp]:
  LENGTH (word_to_bytes (w:'a word) be) = dimindex(:'a) DIV 8
Proof
  rw[word_to_bytes_def]
QED

val () = cv_auto_trans $ INST_TYPE[alpha |-> “:256”]byteTheory.word_to_bytes_aux_def
val () = cv_trans $ INST_TYPE[alpha |-> “:256”]byteTheory.word_to_bytes_def

(* -- *)

Datatype:
  abi_type
  = Uint num
  | Int num
  | Address
  | Bool
  | Fixed num num
  | Ufixed num num
  | Bytes (num option)
  | String
  | Array (num option) abi_type
  | Tuple (abi_type list)
End

Datatype:
  abi_value
  = NumV num
  | IntV int
  | BoolV bool
  | BytesV (byte list)
  | ListV (abi_value list)
End

val abi_type_size_def = definition "abi_type_size_def"
val abi_value_size_def = definition "abi_value_size_def";

Definition valid_int_bound_def:
  valid_int_bound n = (0 < n ∧ n ≤ 256 ∧ n MOD 8 = 0)
End

val () = cv_auto_trans valid_int_bound_def;

Definition valid_fixed_bounds_def:
  valid_fixed_bounds n m =
  (8 ≤ m ∧ m ≤ 256 ∧ m MOD 8 = 0 ∧
   0n < n ∧ n ≤ 80)
End

val () = cv_auto_trans valid_fixed_bounds_def;

Definition valid_length_def[simp]:
  valid_length NONE _ = T ∧
  valid_length (SOME n) ls = (LENGTH ls = n)
End

val () = cv_auto_trans valid_length_def;

Definition valid_bytes_bound_def[simp]:
  valid_bytes_bound NONE = T ∧
  valid_bytes_bound (SOME m) = (0 < m ∧ m ≤ 32)
End

val () = cv_auto_trans valid_bytes_bound_def;

Definition int_bits_bound_def:
  int_bits_bound i n ⇔
  Num (if i < 0 then i + 1 else i) < 2 ** PRE n
End

val () = cv_auto_trans int_bits_bound_def;

Definition has_type_def[simp]:
  has_type (Uint n)     (NumV v)    = (v < 2 ** n ∧ valid_int_bound n) ∧
  has_type (Int n)      (IntV i)    = (int_bits_bound i n ∧ valid_int_bound n) ∧
  has_type (Address)    (NumV v)    = (v < 2 ** 160) ∧
  has_type (Bool)       (NumV v)    = (v < 2) ∧
  has_type (Fixed n m)  (IntV i)    = (int_bits_bound i m ∧ valid_fixed_bounds n m) ∧
  has_type (Ufixed n m) (NumV v)    = (v < 2 ** m ∧ valid_fixed_bounds n m) ∧
  has_type (Bytes b)    (BytesV bs) = (valid_bytes_bound b ∧ valid_length b bs) ∧
  has_type (String)     (BytesV bs) = (T) ∧
  has_type (Array b t)  (ListV vs)  = (have_type t vs ∧ valid_length b vs) ∧
  has_type (Tuple ts)   (ListV vs)  = (has_types ts vs) ∧
  has_type _            _           = (F) ∧
  have_type t [] = (T) ∧
  have_type t (v::vs) = (has_type t v ∧ have_type t vs) ∧
  has_types [] [] = (T) ∧
  has_types (t::ts) (v::vs) = (has_type t v ∧ has_types ts vs) ∧
  has_types _ _ = (F)
Termination
  WF_REL_TAC ‘measure (λx.
  case x of
       INR (INR (ts, vs)) => abi_value1_size vs
     | INR (INL (t, vs)) => abi_value1_size vs
     | INL (t,v) => abi_value_size v)’
End

val () = cv_auto_trans has_type_def;

Theorem have_type_has_types_REPLICATE[simp]:
  (=)
  (have_type t vs)
  (has_types (REPLICATE (LENGTH vs) t) vs)
Proof
  Induct_on`vs` \\ rw[]
QED

Theorem has_types_LIST_REL:
  has_types ts vs ⇔ LIST_REL has_type ts vs
Proof
  qid_spec_tac`vs` \\ Induct_on`ts` \\ rw[]
  \\ Cases_on`vs` \\ gs[]
QED

Definition is_dynamic_def[simp]:
  is_dynamic (Bytes NONE) = T ∧
  is_dynamic (String) = T ∧
  is_dynamic (Array x t) = (IS_NONE x ∨ is_dynamic t) ∧
  is_dynamic (Tuple ts) = any_dynamic ts ∧
  is_dynamic _ = F ∧
  any_dynamic [] = F ∧
  any_dynamic (t::ts) = (is_dynamic t ∨ any_dynamic ts)
Termination
  WF_REL_TAC ‘measure (λx.
  case x of INL t => abi_type_size t
     | INR ts => abi_type1_size ts)’
End

val () = cv_auto_trans is_dynamic_def;

Theorem any_dynamic_EXISTS:
  any_dynamic ts = EXISTS is_dynamic ts
Proof
  Induct_on`ts` \\ rw[]
QED

Overload is_static = “λt. ¬is_dynamic t”

Definition ceil32_def:
  ceil32 n = 32 * ((n + 31) DIV 32)
End

val () = cv_auto_trans ceil32_def;

Theorem ceil32_CEILING_DIV:
  ceil32 n = 32 * (n \\ 32)
Proof
  rw[ceil32_def, CEILING_DIV_def]
QED

Theorem le_ceil32[simp]:
  n ≤ ceil32 n
Proof
  rw[ceil32_CEILING_DIV]
  \\ irule LE_MULT_CEILING_DIV
  \\ rw[]
QED

Theorem ceil32_when_le:
  n ≤ 32 ⇒ ceil32 n = if 0 < n then 32 else 0
Proof
  rw[ceil32_def]
  >- (
    Cases_on`n` \\ gs[ADD1]
    \\ once_rewrite_tac[ADD_SYM]
    \\ irule DIV_MULT_1 \\ gs[] )
  \\ rw[DIV_EQ_0]
QED

Definition static_length_def[simp]:
  static_length (Tuple []) = 0n ∧
  static_length (Tuple (t::ts)) = static_length t + static_length (Tuple ts) ∧
  static_length (Array (SOME n) t) = n * static_length t ∧
  static_length _ = 32
End

val () = cv_trans static_length_def;

Theorem static_length_Tuple_SUM:
  static_length (Tuple ts) = SUM (MAP static_length ts)
Proof
  Induct_on`ts` \\ rw[]
QED

Definition head_lengths_def:
  head_lengths (t::ts) a =
  head_lengths ts
    (a + if is_dynamic t then 32 else static_length t) ∧
  head_lengths _ a = a
End

val () = cv_auto_trans head_lengths_def;

Definition enc_number_def[simp]:
  enc_number (Uint n) (NumV v) =
    word_to_bytes (n2w v : bytes32) T ∧
  enc_number (Int n) (IntV i) =
    word_to_bytes (i2w i : bytes32) T ∧
  enc_number Address (NumV v) =
    word_to_bytes (n2w v : bytes32) T ∧
  enc_number Bool (NumV v) =
    word_to_bytes (n2w v : bytes32) T ∧
  enc_number (Fixed m n) (IntV i) =
    word_to_bytes (i2w i : bytes32) T ∧
  enc_number (Ufixed m n) (NumV v) =
    word_to_bytes (n2w v : bytes32) T ∧
  enc_number _ _ = REPLICATE 32 0w
End

Theorem LENGTH_enc_number[simp]:
  LENGTH (enc_number t v) = 32
Proof
  Cases_on`t` \\ Cases_on`v` \\ rw[]
QED

val () = cv_auto_trans enc_number_def;

Theorem abi_value1_size_map:
  abi_value1_size vs = LENGTH vs + SUM (MAP abi_value_size vs)
Proof
  Induct_on`vs` \\ rw[abi_value_size_def]
QED

Theorem abi_type1_size_map:
  abi_type1_size vs = LENGTH vs + SUM (MAP abi_type_size vs)
Proof
  Induct_on`vs` \\ rw[abi_type_size_def]
QED

Definition enc_def[simp]:
  enc (Tuple ts) (ListV vs) = (
    let hl = head_lengths ts 0 in
      enc_tuple hl 0 ts vs [] []
  ) ∧
  enc (Array (SOME _) t) (ListV vs) = (
    let ts = REPLICATE (LENGTH vs) t in
    let hl = head_lengths ts 0 in
      enc_tuple hl 0 ts vs [] []
  ) ∧
  enc (Array NONE t) (ListV vs) = (
    let k = LENGTH vs in
    let ts = REPLICATE (LENGTH vs) t in
    let hl = head_lengths ts 0 in
    let pre = enc_number (Uint 256) (NumV k) in
      enc_tuple hl 0 ts vs [pre] []
  ) ∧
  enc (Bytes NONE) (BytesV bs) = (
    let k = LENGTH bs in
    let n = ceil32 k in
      enc_number (Uint 256) (NumV k) ++
      bs ++ REPLICATE (n - k) 0w
  ) ∧
  enc String (BytesV bs) = (
    let k = LENGTH bs in
    let n = ceil32 k in
      enc_number (Uint 256) (NumV k) ++
      bs ++ REPLICATE (n - k) 0w
  ) ∧
  enc (Bytes (SOME m)) (BytesV bs) = (
      TAKE 32 bs ++ REPLICATE (32 - m) 0w
  ) ∧
  enc t v = enc_number t v ∧
  enc_tuple hl tl (t::ts) (v::vs) rhds rtls = (
    let dyn = is_dynamic t in
    let tail = if dyn then enc t v else [] in
    let head = if dyn then enc_number (Uint 256) (NumV (hl + tl)) else enc t v in
    enc_tuple hl (tl + LENGTH tail) ts vs (head::rhds) (tail::rtls)
  ) ∧
  enc_tuple _ _ _ _ rhds rtls = FLAT $ REV rhds (REV rtls [])
Termination
  WF_REL_TAC ‘measure (λx.
    case x of INL (_, v) =>  abi_value_size v
       | INR (_,_,_,vs,_,_) => abi_value1_size vs)’
End

val () = cv_trans enc_def;

Theorem enc_has_static_length:
  (∀t v. has_type t v ∧ is_static t ⇒ LENGTH (enc t v) = static_length t) ∧
  (∀hl tl ts vs hds tls. has_types ts vs ∧ ¬any_dynamic ts ⇒
    LENGTH (enc_tuple hl tl ts vs hds tls) =
    SUM (MAP LENGTH hds) + SUM (MAP LENGTH tls) +
    static_length (Tuple ts))
Proof
  ho_match_mp_tac enc_ind
  \\ rw[any_dynamic_EXISTS, has_types_LIST_REL]
  \\ gs[static_length_Tuple_SUM, LENGTH_TAKE_EQ, LENGTH_FLAT, REV_REVERSE_LEM,
        SUM_APPEND, MAP_REVERSE, SUM_REVERSE]
  \\ Cases_on`t` \\ gs[]
QED

Definition type_to_string_def:
  type_to_string (Uint n) = "uint" ++ (num_to_dec_string n) ∧
  type_to_string (Int n) = "int" ++ (num_to_dec_string n) ∧
  type_to_string (Address) = "address" ∧
  type_to_string (Bool) = "bool" ∧
  type_to_string (Fixed m n) =
    "fixed" ++ (num_to_dec_string m) ++ "x" ++ (num_to_dec_string n) ∧
  type_to_string (Ufixed m n) =
    "ufixed" ++ (num_to_dec_string m) ++ "x" ++ (num_to_dec_string n) ∧
  type_to_string (Bytes NONE) = "bytes" ∧
  type_to_string (Bytes (SOME m)) = "bytes" ++ (num_to_dec_string m) ∧
  type_to_string (String) = "string" ∧
  type_to_string (Array NONE t) = type_to_string t ++ "[]" ∧
  type_to_string (Array (SOME k) t) =
    type_to_string t ++ "[" ++ (num_to_dec_string k) ++ "]" ∧
  type_to_string (Tuple ts) = types_to_string ts ["("] ∧
  types_to_string [] acc = FLAT (REV acc [")"]) ∧
  types_to_string [t] acc = FLAT (REV (type_to_string t::acc) [")"]) ∧
  types_to_string (t::ts) acc =
    types_to_string ts (","::type_to_string t::acc)
Termination
  WF_REL_TAC ‘measure (λx. case x of INL t => abi_type_size t | INR (ts,_) =>
                           abi_type1_size ts)’
End

Definition digit_def:
  digit n = CHR (48 + (MIN 9 n))
End

val digit_pre_def = cv_trans_pre digit_def;

Theorem digit_pre[cv_pre]:
  digit_pre n
Proof
  rw[digit_pre_def] \\ rw[MIN_DEF]
QED

Theorem MAP_HEX_n2l_10:
  MAP HEX (n2l 10 n) = MAP digit (n2l 10 n)
Proof
  rw[MAP_EQ_f]
  \\ qspec_then`10`mp_tac n2l_BOUND
  \\ rw[EVERY_MEM]
  \\ first_x_assum drule
  \\ rw[digit_def, MIN_DEF]
  \\ Cases_on`e = 10` \\ rw[]
  \\ `e < 10` by fs[]
  \\ fs[NUMERAL_LESS_THM]
QED

val () = cv_auto_trans (
  ASCIInumbersTheory.num_to_dec_string_def
  |> SIMP_RULE std_ss [ASCIInumbersTheory.n2s_def, FUN_EQ_THM, MAP_HEX_n2l_10]
  )

val () = cv_trans type_to_string_def;

(*
cv_eval``type_to_string (Array (SOME 2) (Bytes (SOME 3)))``
cv_eval``type_to_string (Tuple [(Array NONE (Bytes (SOME 3))); Uint 256])``
cv_eval``type_to_string (Tuple [])``
*)

Definition function_signature_def:
  function_signature name args = name ++ type_to_string (Tuple args)
End

val () = cv_trans function_signature_def;

Definition function_selector_def:
  function_selector name args =
  TAKE 4 (Keccak_256_w64 (MAP (n2w o ORD) (function_signature name args)))
End

val () = cv_auto_trans function_selector_def;

(*
cv_eval ``function_signature "foo" [Uint 32; Bool]``
cv_eval ``function_selector "bar" [Array (SOME 2) (Bytes (SOME 3))]``
0xfc
0xe3
0x53
0xf6
*)

(*
val abc = rhs (concl (EVAL ``MAP (n2w o ORD) "abc" : byte list``))
val def = rhs (concl (EVAL ``MAP (n2w o ORD) "def" : byte list``))
cv_eval``
  (REVERSE $ hex_to_rev_bytes []
   "6162630000000000000000000000000000000000000000000000000000000000") ++
  (REVERSE $ hex_to_rev_bytes []
   "6465660000000000000000000000000000000000000000000000000000000000")
  =
  enc (Array (SOME 2) (Bytes (SOME 3)))
      (ListV [BytesV ^abc; BytesV ^def])``
*)

Definition dec_number_def[simp]:
  dec_number (Uint _) bs = NumV $ w2n (word_of_bytes T (0w: bytes32) bs) ∧
  dec_number (Int _) bs = IntV $ w2i (word_of_bytes T (0w: bytes32) bs) ∧
  dec_number Address bs = NumV $ w2n (word_of_bytes T (0w: bytes32) bs) ∧
  dec_number Bool bs = NumV $ w2n (word_of_bytes T (0w: bytes32) bs) ∧
  dec_number (Fixed _ _) bs = IntV $ w2i (word_of_bytes T (0w: bytes32) bs) ∧
  dec_number (Ufixed _ _) bs = NumV $ w2n (word_of_bytes T (0w: bytes32) bs) ∧
  dec_number _ _ = BytesV []
End

val () = cv_trans dec_number_def;

Definition is_num_value_def[simp]:
  is_num_value (NumV _) = T ∧
  is_num_value (IntV _) = T ∧
  is_num_value _ = F
End

Theorem dec_enc_number:
  has_type t v ∧ is_num_value v
  ⇒ dec_number t (enc_number t v) = v
Proof
  Cases_on`t` \\ Cases_on`v` \\ rw[]
  \\ gs[valid_int_bound_def, valid_fixed_bounds_def]
  \\ TRY $ irule w2i_i2w \\ rw[]
  \\ TRY (
    irule LESS_LESS_EQ_TRANS
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ irule LESS_EQ_TRANS
    \\ qexists_tac`2 ** 256`
    \\ reverse conj_tac >- EVAL_TAC
    \\ simp[] \\ NO_TAC)
  \\ gs[int_bits_bound_def]
  \\ last_assum(mp_then Any (qspec_then`2 ** 255`mp_tac) LESS_LESS_EQ_TRANS)
  \\ (impl_tac >- rw[PRE_SUB1])
  \\ Cases_on`i` \\ gs[]
  \\ rw[INT_ADD_CALCULATE]
QED

Definition dest_NumV_def[simp]:
  dest_NumV (NumV n) = n ∧
  dest_NumV _ = 0
End

val () = cv_trans dest_NumV_def;

Definition dec_def[simp]:
  dec (Tuple ts) bs = dec_tuple ts bs bs [] ∧
  dec (Array (SOME n) t) bs = dec_array n (is_dynamic t) t bs bs [] ∧
  dec (Array NONE t) bs = (
    let n = dest_NumV (dec_number (Uint 256) (TAKE 32 bs)) in
      dec_array n (is_dynamic t) t bs (DROP 32 bs) []
  ) ∧
  dec (Bytes NONE) bs = (
    let k = dest_NumV (dec_number (Uint 256) (TAKE 32 bs)) in
      BytesV (TAKE k (DROP 32 bs))
  ) ∧
  dec String bs = (
    let k = dest_NumV (dec_number (Uint 256) (TAKE 32 bs)) in
      BytesV (TAKE k (DROP 32 bs))
  ) ∧
  dec (Bytes (SOME m)) bs = BytesV $ TAKE m bs ∧
  dec t bs = dec_number t (TAKE 32 bs) ∧
  dec_array 0 _ _ _ _ acc = ListV (REVERSE acc) ∧
  dec_array (SUC n) T t bs0 hds acc = (
    let j = dest_NumV (dec_number (Uint 256) (TAKE 32 hds)) in
    let v = dec t (DROP j bs0) in
    dec_array n T t bs0 (DROP 32 hds) (v::acc)
  ) ∧
  dec_array (SUC n) F t bs0 hds acc = (
    let v = dec t (TAKE 32 hds) in
    dec_array n F t bs0 (DROP 32 hds) (v::acc)
  ) ∧
  dec_tuple [] _ _ acc = ListV (REVERSE acc) ∧
  dec_tuple (t::ts) bs0 hds acc =
    if is_dynamic t then
      let j = dest_NumV (dec_number (Uint 256) (TAKE 32 hds)) in
      let v = dec t (DROP j bs0) in
      dec_tuple ts bs0 (DROP 32 hds) (v::acc)
    else
      let n = static_length t in
      let v = dec t (TAKE n hds) in
      dec_tuple ts bs0 (DROP n hds) (v::acc)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    (INR (INR (ts,_,_,_))) => (abi_type1_size ts, 0)
  | (INR (INL (n,_,t,_,_,_))) => (abi_type_size t, n)
  | (INL (t,_)) => (abi_type_size t, 0))’
End

val () = cv_trans_rec dec_def (
  WF_REL_TAC ‘inv_image ($< LEX $<)
  (λx. case x of
         (INR (INR (ts,_,_,_))) => (cv_size ts, 0)
       | (INR (INL (n,_,t,_,_,_))) => (cv_size t, cv$c2n n)
       | (INL (t,_)) => (cv_size t, 0))’
  \\ rpt conj_tac
  \\ Cases_on`cv_v` \\ rw[] \\ gs[cv_lt_Num_0]
  \\ qmatch_goalsub_rename_tac`cv_snd p`
  \\ Cases_on`p` \\ gs[]
);

(*
Theorem dec_enc:
  (∀t v. has_type t v ⇒ dec t (enc t v) = v) ∧
  (∀hl tl ts vs hds tls bs0 bs acc.
     has_types ts vs ∧
     enc_tuple hl tl ts vs hds tls = bs0 ∧
     bs = DROP (SUM (MAP LENGTH hds)) bs0
     ⇒
     dec_tuple ts bs0 bs acc = ListV (REVERSE acc ++ vs) ∧
     ∀n t. ts = REPLICATE n t ⇒
       dec_array n (is_dynamic t) t bs0 bs acc =
         ListV (REVERSE acc ++ vs))
Proof
  ho_match_mp_tac enc_ind
  \\ rw[] \\ gs[TAKE_APPEND, TAKE_LENGTH_TOO_LONG]
  \\ TRY ( qmatch_assum_rename_tac`has_types (REPLICATE n t) []`
    \\ Cases_on`n` \\ gs[] )
  \\ TRY ( qmatch_assum_rename_tac`has_types ts []`
    \\ Cases_on`ts` \\ gs[] )
  \\ TRY ( qmatch_assum_rename_tac`has_type t (IntV _)`
    \\ Cases_on `t` \\ gs[]
    \\ DEP_REWRITE_TAC[TAKE_LENGTH_TOO_LONG]
    \\ gs[valid_int_bound_def, valid_fixed_bounds_def, int_bits_bound_def]
    \\ irule w2i_i2w \\ gs[]
    \\ qpat_x_assum`Num _ < _`mp_tac \\ rw[]
    \\ TRY (
      simp[INT_LE_LT] \\ disj1_tac
      \\ irule INT_LT_TRANS
      \\ goal_assum drule \\ simp[] )
    \\ cheat )
  \\ TRY ( qmatch_assum_rename_tac`has_type t (NumV _)`
    \\ Cases_on `t` \\ gs[]
    \\ DEP_REWRITE_TAC[TAKE_LENGTH_TOO_LONG]
    \\ gs[valid_int_bound_def, valid_fixed_bounds_def]
    \\ irule LESS_LESS_EQ_TRANS
    \\ goal_assum drule
    \\ irule LESS_EQ_TRANS
    \\ qexists_tac`2 ** 256`
    \\ (reverse conj_tac >- EVAL_TAC)
    \\ DEP_REWRITE_TAC[EXP_BASE_LE_MONO]
    \\ simp[] )

  \\ first_x_assum(qspec_then`[]`mp_tac) \\ rw[]
*)

(*
  val ty = “String”;
  val va = “BytesV [3w]”;
  val th = EQT_ELIM $ cv_eval “has_type ^ty ^va”
  val ed = rhs(concl(cv_eval“enc ^ty ^va”))
  val de = rhs(concl(cv_eval“dec ^ty ^ed”))

  val ty = “Tuple []”;
  val va = “ListV []”;
  val th = EQT_ELIM $ cv_eval “has_type ^ty ^va”
  val ed = rhs(concl(cv_eval“enc ^ty ^va”))
  val de = rhs(concl(cv_eval“dec ^ty ^ed”))

  val ty = “Array NONE String”;
  val va = “ListV []”;
  val th = EQT_ELIM $ cv_eval “has_type ^ty ^va”
  val ed = rhs(concl(cv_eval“enc ^ty ^va”))
  val de = rhs(concl(cv_eval“dec ^ty ^ed”))

  val ty = “Array NONE Bool”;
  val va = “ListV [NumV 1]”;
  val th = EQT_ELIM $ cv_eval “has_type ^ty ^va”
  val ed = rhs(concl(cv_eval“enc ^ty ^va”))
  val de = rhs(concl(cv_eval“dec ^ty ^ed”))

  val ty = “Tuple [Array NONE Bool; Array NONE String]”;
  val va = “ListV [ListV [NumV 1]; ListV []]”;
  val th = EQT_ELIM $ cv_eval “has_type ^ty ^va”
  val ed = rhs(concl(cv_eval“enc ^ty ^va”))
  val de = rhs(concl(cv_eval“dec ^ty ^ed”))

  val ty = “Tuple [Array NONE Bool; Array (SOME 1) String]”;
  val va = “ListV [ListV [NumV 1]; ListV [BytesV []]]”;
  val th = EQT_ELIM $ cv_eval “has_type ^ty ^va”
  val ed = rhs(concl(cv_eval“enc ^ty ^va”))
  val de = rhs(concl(cv_eval“dec ^ty ^ed”))

  val ty = “Tuple [Array (SOME 1) String; Array NONE Bool]”;
  val va = “ListV [ListV [BytesV [1w]]; ListV [NumV 0]]”;
  val th = EQT_ELIM $ cv_eval “has_type ^ty ^va”
  val ed = rhs(concl(cv_eval“enc ^ty ^va”))
  val de = rhs(concl(cv_eval“dec ^ty ^ed”))

  val ty = “Tuple [Array (SOME 2) String; Array NONE Bool]”;
  val va = “ListV [ListV [BytesV [1w]; BytesV [2w; 3w]]; ListV [NumV 0]]”;
  val th = EQT_ELIM $ cv_eval “has_type ^ty ^va”
  val ed = rhs(concl(cv_eval“enc ^ty ^va”))
  val de = rhs(concl(cv_eval“dec ^ty ^ed”))

  val ty = “Tuple [Array (SOME 3) Address; Array NONE Bool]”;
  val va = “ListV [ListV [NumV 1; NumV 2; NumV 3]; ListV [NumV 0]]”;
  val th = EQT_ELIM $ cv_eval “has_type ^ty ^va”
  val ed = rhs(concl(cv_eval“enc ^ty ^va”))
  val de = rhs(concl(cv_eval“dec ^ty ^ed”))

  val ty = “Address”;
  val va = “NumV 1”;
  val th = EQT_ELIM $ cv_eval “has_type ^ty ^va”
  val ed = rhs(concl(cv_eval“enc ^ty ^va”))
  val de = rhs(concl(cv_eval“dec ^ty ^ed”))

  val ty = “Array (SOME 1) Address”;
  val va = “ListV [NumV 1]”;
  val th = EQT_ELIM $ cv_eval “has_type ^ty ^va”
  val ed = rhs(concl(cv_eval“enc ^ty ^va”))
  val de = rhs(concl(cv_eval“dec ^ty ^ed”))

  val ty = “Array (SOME 2) Address”;
  val va = “ListV [NumV 1; NumV 2]”;
  val th = EQT_ELIM $ cv_eval “has_type ^ty ^va”
  val ed = rhs(concl(cv_eval“enc ^ty ^va”))
  val de = rhs(concl(cv_eval“dec ^ty ^ed”))

  val ty = “Tuple [Array (SOME 2) Address]”;
  val va = “ListV [ListV [NumV 1; NumV 2]]”;
  val th = EQT_ELIM $ cv_eval “has_type ^ty ^va”
  val ed = rhs(concl(cv_eval“enc ^ty ^va”))
  val de = rhs(concl(cv_eval“dec ^ty ^ed”))

  val ty = “Tuple [Array (SOME 4) Address; Array NONE Bool; String]”;
  val va = “ListV [
        ListV [NumV 1; NumV 2; NumV 3; NumV 9];
        ListV [NumV 0];
        BytesV [3w; 5w]
      ]”;
  val th = EQT_ELIM $ cv_eval “has_type ^ty ^va”
  val ed = rhs(concl(cv_eval“enc ^ty ^va”))
  val de = rhs(concl(cv_eval“dec ^ty ^ed”))
*)

(* TODO: probably unused, can be deleted: *)

Definition enc_length_def[simp]:
  enc_length (Bytes NONE) (BytesV bs) = 32 + (ceil32 (LENGTH bs)) ∧
  enc_length String (BytesV bs) = 32 + (ceil32 (LENGTH bs)) ∧
  enc_length (Array NONE t) (ListV vs) =
    32 + enc_length_tuple (REPLICATE (LENGTH vs) t) vs 0 ∧
  enc_length (Array _ t) (ListV vs) =
    enc_length_tuple (REPLICATE (LENGTH vs) t) vs 0 ∧
  enc_length (Tuple ts) (ListV vs) = enc_length_tuple ts vs 0 ∧
  enc_length _ _ = 32 ∧
  enc_length_tuple [] _ a = a ∧
  enc_length_tuple _ [] a = a ∧
  enc_length_tuple (t::ts) (v::vs) a =
  enc_length_tuple ts vs $
    enc_length t v + if is_dynamic t then 32 + a else a
Termination
  WF_REL_TAC ‘measure (λx. case x of INL (t,v) => abi_value_size v
                                 | INR (ts, vs, _) => abi_value1_size vs)’
End

Theorem enc_length_tuple_add:
  enc_length_tuple ts vs n =
  enc_length_tuple ts vs 0 + n
Proof
  qid_spec_tac`vs`
  \\ qid_spec_tac`n`
  \\ Induct_on`ts`
  \\ rw[]
  \\ Cases_on`vs`
  >- rw[]
  \\ rewrite_tac[enc_length_def]
  \\ qmatch_goalsub_abbrev_tac`enc_length_tuple _ vv nn`
  \\ first_assum(qspecl_then[`nn`,`vv`]SUBST1_TAC)
  \\ qmatch_goalsub_abbrev_tac`_ + enc_length_tuple _ vv nm`
  \\ first_x_assum(qspecl_then[`nm`,`vv`]SUBST1_TAC)
  \\ rw[Abbr`nn`, Abbr`nm`]
QED

Theorem enc_length_tuple_nil[simp]:
  enc_length_tuple x [] n = n ∧
  enc_length_tuple [] y n = n
Proof
  rw[]
  \\ Cases_on`x` \\ rw[]
QED

Definition static_length_from_value_def[simp]:
  static_length_from_value (ListV []) = 0n ∧
  static_length_from_value (ListV (v::vs)) = static_length_from_value v +
  static_length_from_value (ListV vs) ∧
  static_length_from_value _ = 32
End
Theorem is_static_LENGTH_enc_from_value:
  (∀t v. has_type t v ∧ is_static t ⇒ LENGTH (enc t v) = static_length_from_value v) ∧
  (∀hl tl ts vs hds tls. has_types ts vs ∧ ¬any_dynamic ts ⇒
    LENGTH (enc_tuple hl tl ts vs hds tls) =
    SUM (MAP LENGTH hds) + SUM (MAP LENGTH tls) +
    static_length_from_value (ListV vs))
Proof
  ho_match_mp_tac enc_ind \\ rw[any_dynamic_EXISTS]
  \\ gs[LENGTH_FLAT, REV_REVERSE_LEM, MAP_REVERSE,
        SUM_REVERSE, SUM_APPEND, LENGTH_TAKE_EQ]
QED

Theorem enc_has_length[simp]:
  (∀t v. has_type t v ⇒ LENGTH (enc t v) = enc_length t v) ∧
  (∀hl tl ts vs hds tls. has_types ts vs ⇒
      LENGTH (enc_tuple hl tl ts vs hds tls) =
      enc_length_tuple ts vs (SUM (MAP LENGTH hds) + SUM (MAP LENGTH tls)))
Proof
  ho_match_mp_tac enc_ind
  \\ rpt conj_tac
  \\ reverse(rw[SUB_LEFT_ADD])
  \\ rw[LENGTH_FLAT, REV_REVERSE_LEM, SUM_APPEND, MAP_REVERSE, SUM_REVERSE]
  \\ rw[Once enc_length_tuple_add] \\ gs[]
  \\ rw[Once enc_length_tuple_add, SimpRHS]
  \\ gs[LENGTH_TAKE_EQ] \\ rw[ceil32_when_le] \\ rw[]
  \\ metis_tac[le_ceil32, LESS_EQUAL_ANTISYM]
QED

val () = export_theory();
