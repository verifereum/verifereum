open HolKernel boolLib bossLib Parse wordsLib
     arithmeticTheory
     vfmTypesTheory cv_stdTheory cv_transLib

val () = new_theory "bn254"; (* aka alt_bn128 *)

Definition bn254p_def:
  bn254p = 21888242871839275222246405745257275088696311157297823662689037894645226208583n
End

val () = cv_trans_deep_embedding EVAL bn254p_def;

Definition bn254n_def:
  bn254n = 21888242871839275222246405745257275088548364400416034343698204186575808495617n
End

val () = cv_trans_deep_embedding EVAL bn254n_def;

Definition bn254b_def:
  bn254b = 3n
End

val () = cv_trans_deep_embedding EVAL bn254b_def;

Definition zero_def:
  zero = (0n, 1n, 0n)
End

val () = cv_trans_deep_embedding EVAL zero_def;

Definition fmul_def:
  fmul x y = (x * y) MOD bn254p
End

val () = cv_trans fmul_def;

Definition fadd_def:
  fadd x y = (x + y) MOD bn254p
End

val () = cv_trans fadd_def;

Definition fsub_def:
  fsub x y = if x < y then x + bn254p - y
             else (x - y) MOD bn254p
End

val () = cv_trans fsub_def;

Definition add_def:
  add (x1, y1, z1) (x2, y2, z2) = let
  b3 = fmul bn254b 3;
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
  z3 = fmul b3 t2;
  x3 = fsub t1 z3;
  z3 = fadd t1 z3;
  y3 = fmul x3 z3;
  t1 = fadd t0 t0;
  t1 = fadd t1 t0;
  t4 = fmul b3 t4;
  t0 = fmul t1 t4;
  y3 = fadd y3 t0;
  t0 = fmul t5 t4;
  x3 = fmul t3 x3;
  x3 = fsub x3 t0;
  t0 = fmul t3 t1;
  z3 = fmul t5 z3;
  z3 = fadd z3 t0
  in (x3, y3, z3)
End

val () = cv_trans add_def;

Definition finv_loop_def:
  finv_loop a b x y u v =
  if a = 0 then x else let
    q = b DIV a;
    r = b MOD a;
    m = fsub x (fmul u q);
    n = fsub y (fmul v q);
    b = a; a = r; x = u; y = v; u = m; v = n in
      finv_loop a b x y u v
End

val finv_loop_pre_def = cv_trans_pre finv_loop_def;

Theorem finv_loop_pre[cv_pre]:
  ∀a b x y u v. finv_loop_pre a b x y u v
Proof
  ho_match_mp_tac finv_loop_ind
  \\ rw[]
  \\ rw[Once finv_loop_pre_def]
  \\ gvs[]
QED

Definition finv_def:
  finv n = finv_loop n bn254p 0 1 1 0
End

val () = cv_trans finv_def;

Definition dbl_def:
  dbl (x1, y1, z1) = let
  b3 = fmul bn254b 3;
  t0 = fmul x1 x1;
  t1 = fmul y1 y1;
  t2 = fmul z1 z1;
  t3 = fmul x1 y1;
  t3 = fadd t3 t3;
  z3 = fmul x1 z1;
  z3 = fadd z3 z3;
  y3 = fmul b3 t2;
  x3 = fsub t1 y3;
  y3 = fadd t1 y3;
  y3 = fmul x3 y3;
  x3 = fmul t3 x3;
  t3 = fmul b3 z3;
  z3 = fadd t0 t0;
  t0 = fadd z3 t0;
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

Definition mul_loop_def:
  mul_loop a p n =
  if n = 0 then a
  else let
    a = if ODD n then add a p else a;
    p = dbl p;
    n = n DIV 2
  in mul_loop a p n
End

val () = cv_trans mul_loop_def;

Definition mul_def:
  mul p n =
  if n = 0 then zero else
  if SND(SND p) = 0 ∨ n = 1 then p else
    mul_loop zero p (n MOD bn254n)
End

val () = cv_trans mul_def;

Definition weierstrassEquation_def:
  weierstrassEquation x = let
    x2 = fmul x x;
    x3 = fmul x2 x
  in fadd x3 bn254b
End

val () = cv_trans weierstrassEquation_def;

Definition validAffine_def:
  validAffine (x, y) =
  (x < bn254p ∧ y < bn254p ∧
   ((x, y) = (0, 0) ∨
    fmul y y = weierstrassEquation x))
End

val () = cv_trans validAffine_def;

Definition toAffine_def:
  toAffine (x, y, z) =
  if z = 1 then (x, y) else
  if z = 0 then (0, 0) else
  let iz = finv z in
    (fmul x iz, fmul y iz)
End

val () = cv_trans toAffine_def;

Definition fromAffine_def:
  fromAffine (x, y) =
  if (x, y) = (0, 0) then zero else (x, y, 1)
End

val () = cv_trans fromAffine_def;

Definition addAffine_def:
  addAffine a b =
  toAffine (add (fromAffine a) (fromAffine b))
End

val () = cv_trans addAffine_def;

Definition mulAffine_def:
  mulAffine a n =
  toAffine (mul (fromAffine a) n)
End

val () = cv_trans mulAffine_def;

val () = export_theory();
