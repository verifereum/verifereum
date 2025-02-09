open HolKernel boolLib bossLib Parse
     listTheory vfmTypesTheory
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

val () = export_theory();
