open HolKernel boolLib bossLib Parse wordsLib
     arithmeticTheory
     vfmTypesTheory cv_stdTheory cv_transLib

val () = new_theory "bls12381";


Definition bls_modulus_def:
  bls_modulus = 52435875175126190479447740508185965837690552500527637822603658699938581184513n
End

val () = cv_trans_deep_embedding EVAL bls_modulus_def;


Definition g1_point_at_infinity_def:
  g1_point_at_infinity = [0xc0w] ++ REPLICATE 47 (0w:word8)
End

val () = cv_trans_deep_embedding EVAL g1_point_at_infinity_def;


Definition fadd_def:
  fadd x y = (x + y) MOD bls_modulus
End

val () = cv_trans fadd_def;

Definition fsub_def:
  fsub x y = if x < y then x + bls_modulus - y
             else (x - y) MOD bls_modulus
End

val () = cv_trans fsub_def;

Definition G1_def:
  G1 = (3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507n,
        1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569n)
End

val () = cv_trans_deep_embedding EVAL G1_def;

Definition G2_def:
  G2 = ((352701069587466618187139116011060144890029952792775240219908644239793785735715026873347600343865175952761926303160n,
         3059144344244213709971259814753781636986470325476647558659373206291635324768958432433509563104347017837885763365758n),
        (1985150602287291935568054521177171638300868978215655730859378665066344726373823718423869104263333984641494340347905n,
         927553665492332455747201965776037880757740193453592970025027978793976877002675564980949289727957565575433344219582n))
End

val () = cv_trans_deep_embedding EVAL G2_def;


(* https://github.com/ethereum/execution-specs/blob/master/src/ethereum/crypto/kzg.py#L71 *)
Definition KZG_SETUP_G2_MONOMIAL_1_def:
  KZG_SETUP_G2_MONOMIAL_1 = "b5bfd7dd8cdeb128843bc287230af38926187075cbfbefa81009a2ce615ac53d2914e5870cb452d2afaaab24f3499f72185cbfee53492714734429b7b38608e23926c911cceceac9a36851477ba4c60b087041de621000edc98edada20c1def2"
End

val () = cv_trans_deep_embedding EVAL KZG_SETUP_G2_MONOMIAL_1_def;

(* Required: https://github.com/ethereum/py_ecc/blob/main/py_ecc/bls/point_compression.py
 *)
Definition get_flags_def:
  get_flags (z: num) <=>
    (BIT 383 z, BIT 382 z, BIT 381 z)
End
val () = cv_auto_trans get_flags_def;

Definition pow_2_381_def:
  pow_2_381 <=> 2n EXP 381
End

val () = cv_trans_deep_embedding EVAL pow_2_381_def;

val () = monadsyntax.enable_monad "option";
val () = monadsyntax.enable_monadsyntax ();

Definition is_point_at_infinity_def:
  is_point_at_infinity (z1:num) (z2: num option): bool <=>
    z1 MOD pow_2_381 = 0n /\ (case z2 of NONE => T | SOME z2' => z2' = 0)
End

val () = cv_auto_trans is_point_at_infinity_def;


Definition decompress_G2_def:
  decompress_G2 (z1:num) (z2:num) = do
    (c_flag1, b_flag1, a_flag1) <<- get_flags z1;
    assert (~c_flag1);
    is_inf_pt <<- is_point_at_infinity z1 (SOME z2);
    assert (b_flag1 <> is_inf_pt);
    if is_inf_pt
    then do
      assert a_flag1;
      fail (* return constant Z1 which is None*)
    od
    else do
      x <<- z1 MOD pow_2_381;
      assert (x >= bls_modulus);
      (* return $ (x EXP 3 + b) MOD bls_modulus *)
    od
  od
End

Definition setup1_def:
  setup1 =
    let b = REVERSE $ hex_to_rev_bytes [] KZG_SETUP_G2_MONOMIAL_1 in
    let p1 = num_of_be_bytes $ TAKE 48 b in
    let p2 = num_of_be_bytes $ DROP 48 b in
    in ARB:(num#num)#(num#num)  (* KZG_SETUP_G2_MONOMIAL_1 decoded *)
End

Definition commitment_def:
  commitment = ARB: (num#num)  (* Public key or commitment point *)
End

(* X_minus_z = setup1 + G2 * (r - z)
  https://github.com/ethereum/execution-specs/blob/3803c8a32b53bdd03ed52c3ace5452288f88a513/src/ethereum/crypto/kzg.py#L172-L175
 *)
(* Definition X_minus_z_def:
  X_minus_z z = addAffineF2 setup1 (mulAffineF2 G2 (fsub bls_modulus z))
End *)

(* P_minus_y = commitment + G1 * (r - y)
  https://github.com/ethereum/execution-specs/blob/3803c8a32b53bdd03ed52c3ace5452288f88a513/src/ethereum/crypto/kzg.py#L176-L179
 *)
(* Definition P_minus_y_def:
  P_minus_y y = addAffine commitment (mulAffine G1 (fsub bls_modulus y))
End *)

Definition pairing_check_def:
  pairing_check z y proof = T
End

val () = export_theory ();
