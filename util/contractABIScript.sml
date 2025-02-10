open HolKernel boolLib bossLib Parse wordsLib
     listTheory arithmeticTheory numposrepTheory wordsTheory
     vfmTypesTheory
     cv_transLib

val () = new_theory "contractABI";

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

Definition valid_length_def:
  valid_length NONE _ = T ∧
  valid_length (SOME n) ls = (LENGTH ls = n)
End

val () = cv_auto_trans valid_length_def;

Definition has_type_def:
  has_type (Uint n)     (NumV v)    = (v < 2 ** n ∧ valid_int_bound n) ∧
  has_type (Int n)      (IntV i)    = (Num i < 2 ** n ∧ valid_int_bound n) ∧
  has_type (Address)    (NumV v)    = (v < 2 ** 160) ∧
  has_type (Bool)       (NumV v)    = (v < 2) ∧
  has_type (Fixed n m)  (IntV i)    = (Num i < 2 ** m ∧ valid_fixed_bounds n m) ∧
  has_type (Ufixed n m) (NumV v)    = (v < 2 ** m ∧ valid_fixed_bounds n m) ∧
  has_type (Bytes b)    (BytesV bs) = (valid_length b bs) ∧
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

Definition is_dynamic_def:
  is_dynamic (Bytes NONE) = T ∧
  is_dynamic (String) = T ∧
  is_dynamic (Array _ t) = is_dynamic t ∧
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

Overload is_static = “λt. ¬is_dynamic t”

Definition ceil32_def:
  ceil32 n = 32 * ((n + 31) DIV 32)
End

val () = cv_auto_trans ceil32_def;

Definition enc_length_def:
  enc_length _ (BytesV bs) = 32 + (ceil32 (LENGTH bs)) ∧
  enc_length (Array _ t) (ListV vs) =
    32 + enc_length_tuple (REPLICATE (LENGTH vs) t) vs 0 ∧
  enc_length (Tuple ts) (ListV vs) = enc_length_tuple ts vs 0 ∧
  enc_length _ _ = 32 ∧
  enc_length_tuple [] _ a = a ∧
  enc_length_tuple _ [] a = a ∧
  enc_length_tuple (t::ts) (v::vs) a =
  enc_length_tuple ts vs $
    32 + if is_dynamic t then a + enc_length t v else a
Termination
  WF_REL_TAC ‘measure (λx. case x of INL (t,v) => abi_value_size v
                                 | INR (ts, vs, _) => abi_value1_size vs)’
End

val () = cv_auto_trans enc_length_def;

Definition head_lengths_def:
  head_lengths (t::ts) (v::vs) a =
  head_lengths ts vs
    (a + if is_dynamic t then 32 else enc_length t v) ∧
  head_lengths _ _ a = a
End

val () = cv_auto_trans head_lengths_def;

Definition enc_number_def:
  enc_number (Uint n) (NumV v) =
    word_to_bytes (n2w v : bytes32) T ∧
  enc_number (Int n) (IntV i) =
    word_to_bytes
      (if 0 ≤ i then n2w (Num i) else -n2w (Num i) : bytes32) T ∧
  enc_number Address (NumV v) =
    word_to_bytes (n2w v : bytes32) T ∧
  enc_number Bool (NumV v) =
    word_to_bytes (n2w v : bytes32) T ∧
  enc_number (Fixed m n) (IntV i) =
    word_to_bytes
      (if 0 ≤ i then n2w (Num i) else -n2w (Num i) : bytes32) T ∧
  enc_number (Ufixed m n) (NumV v) =
    word_to_bytes (n2w v : bytes32) T ∧
  enc_number _ _ = []
End

val () = cv_auto_trans $ INST_TYPE[alpha |-> “:256”]byteTheory.word_to_bytes_aux_def
val () = cv_trans $ INST_TYPE[alpha |-> “:256”]byteTheory.word_to_bytes_def
val () = cv_auto_trans enc_number_def;

Theorem abi_value1_size_map:
  abi_value1_size vs = LENGTH vs + SUM (MAP abi_value_size vs)
Proof
  Induct_on`vs` \\ rw[abi_value_size_def]
QED

Definition enc_def:
  enc (Tuple ts) (ListV vs) = (
    let hl = head_lengths ts vs 0 in
      enc_tuple hl 0 ts vs [] []
  ) ∧
  enc (Array (SOME _) t) (ListV vs) = (
    let ts = REPLICATE (LENGTH vs) t in
    let hl = head_lengths ts vs 0 in
      enc_tuple hl 0 ts vs [] []
  ) ∧
  enc (Array NONE t) (ListV vs) = (
    let k = LENGTH vs in
    let ts = REPLICATE (LENGTH vs) t in
    let hl = head_lengths ts vs 0 in
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
      bs ++ REPLICATE (32 - m) 0w
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

Definition dec_def:
  dec n = CHR (48 + (MIN 9 n))
End

val dec_pre_def = cv_trans_pre dec_def;

Theorem dec_pre[cv_pre]:
  dec_pre n
Proof
  rw[dec_pre_def] \\ rw[MIN_DEF]
QED

Theorem MAP_HEX_n2l_10:
  MAP HEX (n2l 10 n) = MAP dec (n2l 10 n)
Proof
  rw[MAP_EQ_f]
  \\ qspec_then`10`mp_tac n2l_BOUND
  \\ rw[EVERY_MEM]
  \\ first_x_assum drule
  \\ rw[dec_def, MIN_DEF]
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

val () = export_theory();
