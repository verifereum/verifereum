Theory secp256r1
Ancestors
  vfmTypes
Libs
  cv_transLib
  wordsLib

Definition secp256r1N_def:
  secp256r1N =
    0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551n
End

val () = cv_trans_deep_embedding EVAL secp256r1N_def;

Definition secp256r1P_def:
  secp256r1P =
    0xffffffff00000001000000000000000000000000ffffffffffffffffffffffffn
End

val () = cv_trans_deep_embedding EVAL secp256r1P_def;

Definition secp256r1a_def:
  secp256r1a =
    0xffffffff00000001000000000000000000000000fffffffffffffffffffffffcn
End

val () = cv_trans_deep_embedding EVAL secp256r1a_def;

Definition secp256r1b_def:
  secp256r1b =
    0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604bn
End

val () = cv_trans_deep_embedding EVAL secp256r1b_def;

Definition secp256r1Gx_def:
  secp256r1Gx =
    0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296n
End

val () = cv_trans_deep_embedding EVAL secp256r1Gx_def;

Definition secp256r1Gy_def:
  secp256r1Gy =
    0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5n
End

val () = cv_trans_deep_embedding EVAL secp256r1Gy_def;

Definition r1_base_def:
  r1_base = (secp256r1Gx, secp256r1Gy, 1n)
End

val () = cv_trans_deep_embedding EVAL r1_base_def;

Definition r1_zero_def:
  r1_zero = (0n, 1n, 0n)
End

val () = cv_trans_deep_embedding EVAL r1_zero_def;

Definition r1_fmul_def:
  r1_fmul x y = (x * y) MOD secp256r1P
End

val () = cv_trans r1_fmul_def;

Definition r1_fadd_def:
  r1_fadd x y = (x + y) MOD secp256r1P
End

val () = cv_trans r1_fadd_def;

Definition r1_fsub_def:
  r1_fsub x y = if x < y then x + secp256r1P - y
             else (x - y) MOD secp256r1P
End

val () = cv_trans r1_fsub_def;

Definition r1_fneg_def:
  r1_fneg x = if x = 0 then 0 else secp256r1P - x
End

val () = cv_trans r1_fneg_def;

Definition r1_add_def:
  r1_add (x1, y1, z1) (x2, y2, z2) = let
  t0 = r1_fmul x1 x2;
  t1 = r1_fmul y1 y2;
  t2 = r1_fmul z1 z2;
  t3 = r1_fadd x1 y1;
  t4 = r1_fadd x2 y2;
  t3 = r1_fmul t3 t4;
  t4 = r1_fadd t0 t1;
  t3 = r1_fsub t3 t4;
  t4 = r1_fadd x1 z1;
  t5 = r1_fadd x2 z2;
  t4 = r1_fmul t4 t5;
  t5 = r1_fadd t0 t2;
  t4 = r1_fsub t4 t5;
  t5 = r1_fadd y1 z1;
  x3 = r1_fadd y2 z2;
  t5 = r1_fmul t5 x3;
  x3 = r1_fadd t1 t2;
  t5 = r1_fsub t5 x3;
  z3 = r1_fmul secp256r1a t4;
  x3 = r1_fmul (r1_fmul secp256r1b 3) t2;
  z3 = r1_fadd x3 z3;
  x3 = r1_fsub t1 z3;
  z3 = r1_fadd t1 z3;
  y3 = r1_fmul x3 z3;
  t1 = r1_fadd t0 t0;
  t1 = r1_fadd t1 t0;
  t2 = r1_fmul secp256r1a t2;
  t4 = r1_fmul (r1_fmul secp256r1b 3) t4;
  t1 = r1_fadd t1 t2;
  t2 = r1_fsub t0 t2;
  t2 = r1_fmul secp256r1a t2;
  t4 = r1_fadd t4 t2;
  t0 = r1_fmul t1 t4;
  y3 = r1_fadd y3 t0;
  t0 = r1_fmul t5 t4;
  x3 = r1_fmul t3 x3;
  x3 = r1_fsub x3 t0;
  t0 = r1_fmul t3 t1;
  z3 = r1_fmul t5 z3;
  z3 = r1_fadd z3 t0
  in (x3, y3, z3)
End

val () = cv_trans r1_add_def;

Definition r1_dbl_def:
  r1_dbl (x1, y1, z1) = let
  t0 = r1_fmul x1 x1;
  t1 = r1_fmul y1 y1;
  t2 = r1_fmul z1 z1;
  t3 = r1_fmul x1 y1;
  t3 = r1_fadd t3 t3;
  z3 = r1_fmul x1 z1;
  z3 = r1_fadd z3 z3;
  x3 = r1_fmul secp256r1a z3;
  y3 = r1_fmul (r1_fmul secp256r1b 3) t2;
  y3 = r1_fadd x3 y3;
  x3 = r1_fsub t1 y3;
  y3 = r1_fadd t1 y3;
  y3 = r1_fmul x3 y3;
  x3 = r1_fmul t3 x3;
  z3 = r1_fmul (r1_fmul secp256r1b 3) z3;
  t2 = r1_fmul secp256r1a t2;
  t3 = r1_fsub t0 t2;
  t3 = r1_fmul secp256r1a t3;
  t3 = r1_fadd t3 z3;
  z3 = r1_fadd t0 t0;
  t0 = r1_fadd z3 t0;
  t0 = r1_fadd t0 t2;
  t0 = r1_fmul t0 t3;
  y3 = r1_fadd y3 t0;
  t2 = r1_fmul y1 z1;
  t2 = r1_fadd t2 t2;
  t0 = r1_fmul t2 t3;
  x3 = r1_fsub x3 t0;
  z3 = r1_fmul t2 t1;
  z3 = r1_fadd z3 z3;
  z3 = r1_fadd z3 z3
  in (x3, y3, z3)
End

val () = cv_trans r1_dbl_def;

Definition r1_nmul_def:
  r1_nmul x y = (x * y) MOD secp256r1N
End

val () = cv_trans r1_nmul_def;

Definition r1_nsub_def:
  r1_nsub x y = if x < y then x + secp256r1N - y
             else (x - y) MOD secp256r1N
End

val () = cv_trans r1_nsub_def;

Definition r1_neg_def:
  r1_neg (x:num,y,z:num) = (x, r1_fneg y, z)
End

val () = cv_trans r1_neg_def;

Definition r1_mul_loop_def:
  r1_mul_loop acc p n =
  if n = 0 then acc
  else let
    acc = if ODD n then r1_add acc p else acc;
    p = r1_dbl p;
    n = n DIV 2
  in r1_mul_loop acc p n
Termination
  WF_REL_TAC ‘measure (SND o SND)’
End

val () = cv_trans r1_mul_loop_def;

Definition r1_mul_def:
  r1_mul p n =
  if n = 0 then r1_zero else
  if SND(SND p) = 0 then r1_zero else
  if n = 1 then p else
  r1_mul_loop r1_zero p n
End

val () = cv_trans r1_mul_def;

Definition r1_finv_loop_def:
  r1_finv_loop a b x y u v =
  if a = 0 then x else let
    q = b DIV a;
    r = b MOD a;
    m = r1_fsub x (r1_fmul u q);
    n = r1_fsub y (r1_fmul v q);
    b = a; a = r; x = u; y = v; u = m; v = n in
      r1_finv_loop a b x y u v
Termination
  WF_REL_TAC ‘measure FST’
End

val r1_finv_loop_pre_def = cv_trans_pre "r1_finv_loop_pre" r1_finv_loop_def;

Theorem r1_finv_loop_pre[cv_pre]:
  ∀a b x y u v. r1_finv_loop_pre a b x y u v
Proof
  ho_match_mp_tac r1_finv_loop_ind
  \\ rw[]
  \\ rw[Once r1_finv_loop_pre_def]
  \\ gvs[]
QED

Definition r1_finv_def:
  r1_finv n = r1_finv_loop n secp256r1P 0 1 1 0
End

val () = cv_trans r1_finv_def;

Definition r1_finvN_loop_def:
  r1_finvN_loop a b x y u v =
  if a = 0 then x else let
    q = b DIV a;
    r = b MOD a;
    m = r1_nsub x (r1_nmul u q);
    n = r1_nsub y (r1_nmul v q);
    b = a; a = r; x = u; y = v; u = m; v = n in
      r1_finvN_loop a b x y u v
Termination
  WF_REL_TAC ‘measure FST’
End

val r1_finvN_loop_pre_def = cv_trans_pre "r1_finvN_loop_pre" r1_finvN_loop_def;

Theorem r1_finvN_loop_pre[cv_pre]:
  ∀a b x y u v. r1_finvN_loop_pre a b x y u v
Proof
  ho_match_mp_tac r1_finvN_loop_ind
  \\ rw[]
  \\ rw[Once r1_finvN_loop_pre_def]
  \\ gvs[]
QED

Definition r1_finvN_def:
  r1_finvN n = r1_finvN_loop n secp256r1N 0 1 1 0
End

val () = cv_trans r1_finvN_def;

Definition r1_on_curve_def:
  r1_on_curve x y =
    let x2 = r1_fmul x x in
    let x3 = r1_fmul x2 x in
    let ax = r1_fmul secp256r1a x in
    let rhs = r1_fadd (r1_fadd x3 ax) secp256r1b in
    let y2 = r1_fmul y y in
    y2 = rhs
End

val () = cv_trans r1_on_curve_def;

Definition r1_is_zero_def:
  r1_is_zero (x:num, y:num, z:num) = (z = 0)
End

val () = cv_trans r1_is_zero_def;

Definition r1_to_affine_def:
  r1_to_affine (x, y, z) =
    if z = 0 then (0, 0)
    else if z = 1 then (x, y)
    else let iz = r1_finv z in
         (r1_fmul x iz, r1_fmul y iz)
End

val () = cv_trans r1_to_affine_def;

Definition p256verify_def:
  p256verify (msgHash: bytes32) r s qx qy =
    let h = w2n msgHash in
    let r_val = r in
    let s_val = s in
    if r_val = 0 ∨ r_val ≥ secp256r1N then F else
    if s_val = 0 ∨ s_val ≥ secp256r1N then F else
    if qx ≥ secp256r1P ∨ qy ≥ secp256r1P then F else
    if ¬r1_on_curve qx qy then F else
    let Q = (qx, qy, 1n) in
    if r1_is_zero Q then F else
    let s_inv = r1_finvN s_val in
    let u1 = r1_nmul h s_inv in
    let u2 = r1_nmul r_val s_inv in
    let R = r1_add (r1_mul r1_base u1) (r1_mul Q u2) in
    if r1_is_zero R then F else
    let (rx, ry) = r1_to_affine R in
    (rx MOD secp256r1N) = r_val
End

val () = cv_trans p256verify_def;

val () = export_theory();
