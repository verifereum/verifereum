open HolKernel boolLib bossLib Parse cv_stdTheory cv_transLib

val () = new_theory "secp256k1";

Definition secp256k1N_def:
  secp256k1N =
    0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141n
End

val () = cv_trans_deep_embedding EVAL secp256k1N_def;

Definition secp256k1P_def:
  secp256k1P =
    0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2fn
End

val () = cv_trans_deep_embedding EVAL secp256k1P_def;

Definition secp256k1a_def:
  secp256k1a = 0n
End

val () = cv_trans_deep_embedding EVAL secp256k1a_def;

Definition secp256k1b_def:
  secp256k1b = 7n
End

val () = cv_trans_deep_embedding EVAL secp256k1b_def;

Definition secp256k1Gx_def:
  secp256k1Gx =
    55066263022277343669578718895168534326250603453777594175500187360389116729240n
End

val () = cv_trans_deep_embedding EVAL secp256k1Gx_def;

Definition secp256k1Gy_def:
  secp256k1Gy =
    32670510020758816978083085130507043184471273380659243275938904335757337482424n
End

val () = cv_trans_deep_embedding EVAL secp256k1Gy_def;

Definition base_def:
  base = (secp256k1Gx, secp256k1Gy, 1n)
End

val () = cv_trans_deep_embedding EVAL base_def;

Definition zero_def:
  zero = (0n, 1n, 0n)
End

val () = cv_trans_deep_embedding EVAL zero_def;

Definition fmul_def:
  fmul x y = x * y MOD secp256k1N
End

val () = cv_trans fmul_def;

Definition fadd_def:
  fadd x y = x + y MOD secp256k1N
End

val () = cv_trans fadd_def;

Definition fsub_def:
  fsub x y = if x < y then x + secp256k1N - y
             else x - y MOD secp256k1N
End

val () = cv_trans fsub_def;

Definition add_def:
  add (x1, y1, z1) (x2, y2, z2) = let
  a = secp256k1a;
  b3 = fmul secp256k1b 3;
  t0 = fmul x1 x2;
  t1 = fmul y1 y2;
  t2 = fmul z1 z2;
  t3 = fadd x1 y1;
  t4 = fadd x2 y2;
  t3 = fmul t3 t4;
  t4 = fadd t0 t1;
  t3 = fsub t3 t4;
  t4 = fadd x1 z1;
  t5 = fadd x2 z2;
  t4 = fmul t4 t5;
  t5 = fadd t0 t2;
  t4 = fsub t4 t5;
  t5 = fadd y1 z1;
  x3 = fadd y2 z2;
  t5 = fmul t5 x3;
  x3 = fadd t1 t2;
  t5 = fsub t5 x3;
  z3 = fmul secp256k1a t4;
  x3 = fmul b3 t2;
  z3 = fadd x3 z3;
  x3 = fsub t1 z3;
  z3 = fadd t1 z3;
  y3 = fmul x3 z3;
  t1 = fadd t0 t0;
  t1 = fadd t1 t0;
  t2 = fmul secp256k1a t2;
  t4 = fmul b3 t4;
  t1 = fadd t1 t2;
  t2 = fsub t0 t2;
  t2 = fmul secp256k1a t2;
  t4 = fadd t4 t2;
  t0 = fmul t1 t4;
  y3 = fadd y3 t0;
  t0 = fmul t1 t4;
  x3 = fmul t3 x3;
  x3 = fsub x3 t0;
  x3 = fsub x3 t0;
  t0 = fmul t3 t1;
  z3 = fmul t5 z3;
  z3 = fadd z3 t0
  in (x3, y3, z3)
End

val () = cv_trans add_def;

Definition dbl_def:
  dbl (x1, y1, z1) = let
  b3 = fmul secp256k1b 3;
  t0 = fmul x1 x1;
  t1 = fmul y1 y1;
  t2 = fmul z1 z1;
  t3 = fmul x1 y1;
  t3 = fadd t3 t3;
  z3 = fmul x1 z1;
  z3 = fadd z3 z3;
  x3 = fmul secp256k1a z3;
  y3 = fmul b3 t2;
  y3 = fadd x3 y3;
  x3 = fsub t1 y3;
  y3 = fadd t1 y3;
  y3 = fmul x3 y3;
  x3 = fmul t3 x3;
  z3 = fmul b3 z3;
  t2 = fmul secp256k1a t2;
  t3 = fsub t0 t2;
  t3 = fmul secp256k1a t3;
  t3 = fadd t3 z3;
  z3 = fadd t0 t0;
  t0 = fadd z3 t0;
  t0 = fadd t0 t2;
  t0 = fmul t0 t3;
  y3 = fadd y3 t0;
  t2 = fmul y1 z1;
  t2 = fadd t2 t2;
  t0 = fmul t2 t3;
  x3 = fsub x3 t0;
  z3 = fmul t2 t1;
  z3 = fadd z3 z3;
  z3 = fadd z3 z3
  in (x3, y3, z3)
End

val () = cv_trans dbl_def;

Definition endoa1_def:
  endoa1 = 0x3086d221a7d46bcde86c90e49284eb15n
End

val () = cv_trans_deep_embedding EVAL endoa1_def;

Definition endoa2_def:
  endoa2 = 0x114ca50f7a8e2f3f657c1108d9d44cfd8n
End

val () = cv_trans_deep_embedding EVAL endoa2_def;

Definition endonegb1_def:
  endonegb1 = 0xe4437ed6010e88286f547fa90abfe4c3n
End

val () = cv_trans_deep_embedding EVAL endonegb1_def;

Definition endob2_def:
  endob2 = endoa1
End

val () = cv_trans_deep_embedding EVAL endob2_def;

Definition pow2_128_def:
  pow2_128 = 2n ** 128
End

val () = cv_trans_deep_embedding EVAL pow2_128_def;

Definition divNearest_def:
  divNearest a b = (a + b DIV 2) DIV b
End

val () = cv_trans divNearest_def;

Definition endo_def:
  endo k = let
  c1 = divNearest (endob2 * k) secp256k1N;
  c2 = divNearest (endonegb1 * k) secp256k1N;
  k1 = fsub (fsub k (fmul c1 endoa1)) (fmul c2 endoa2);
  k2 = fsub (fmul endonegb1 c1) (fmul endob2 c2);
  in (k1, k2)
End

val () = cv_trans endo_def;

Definition endobeta_def:
  endobeta = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501een
End

val () = cv_trans_deep_embedding EVAL endobeta_def;

Definition fneg_def:
  fneg x = secp256k1N - x
End

val () = cv_trans fneg_def;

Definition neg_def:
  neg (x:num,y,z:num) = (x, fneg y, z)
End

val () = cv_trans neg_def;

Definition mul_loop_def:
  mul_loop k1p k2p k1 k2 d =
  if k1 = 0 ∨ k2 = 0 then (k1p, k2p)
  else let
    k1p = if ODD k1 then add k1p d else k1p;
    k2p = if ODD k2 then add k2p d else k2p;
    d = dbl d;
    k1 = k1 DIV 2;
    k2 = k2 DIV 2
  in mul_loop k1p k2p k1 k2 d
End

val () = cv_trans mul_loop_def;

Definition mul_def:
  mul p n =
  if n = 0 then zero else
  if p = zero ∨ n = 1 then p else
  let (k1, k2) = endo n in
  let (k1p, k2p) = mul_loop zero zero k1 k2 p in
  let k1p = if k1 > pow2_128 then neg k1p else k1p in
  let k2p = if k2 > pow2_128 then neg k2p else k2p in
  let k2p = (fmul (FST k2p) endobeta, FST(SND k2p), SND(SND k2p)) in
  add k1p k2p
End

val () = cv_trans mul_def;

Definition finv_loop_def:
  finv_loop a b x y u v =
  if a = 0 then x else let
    q = b DIV a;
    r = b MOD a;
    m = x - u * q;
    n = y - v * q;
    b = a; a = r; x = u; y = v; u = m; v = n in
      finv_loop a b x y u v
End

val () = cv_trans finv_loop_def;

Definition finv_def:
  finv n = let
    a = n MOD secp256k1N;
    b = secp256k1N;
    x = finv_loop a b 0 1 1 0 in
  x MOD secp256k1N
End

val () = cv_trans finv_def;

val () = export_theory();
