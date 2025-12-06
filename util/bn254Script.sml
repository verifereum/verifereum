Theory bn254 (* aka alt_bn128 *)
Ancestors
  vfmTypes
Libs
  cv_transLib
  wordsLib

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
Termination
  WF_REL_TAC ‘measure FST’
End

val finv_loop_pre_def = cv_trans_pre "finv_loop_pre" finv_loop_def;

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

Definition fdiv_def:
  fdiv x y = fmul x (finv y)
End

val () = cv_trans fdiv_def;

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

Definition bn254bF2_def:
  bn254bF2 =
  (19485874751759354771024239261021720505790618469301721065564631296452457478373n,
   266929791119991161246907387137283842545076965332900288569378510910307636690n)
End

val () = cv_trans_deep_embedding EVAL bn254bF2_def;

Definition f2add_def:
  f2add (x1,xi) (y1,yi) =
    (fadd x1 y1, fadd xi yi)
End

val () = cv_trans f2add_def;

Definition f2mul_def:
  f2mul (x1,xi) (y1,yi) = let
    t1 = fmul x1 y1;
    t2 = fmul xi yi;
    o1 = fsub t1 t2;
    oi = fsub (fmul (fadd x1 xi) (fadd y1 yi)) (fadd t1 t2);
  in (o1, oi)
End

val () = cv_trans f2mul_def;

Definition f2muls_def:
  f2muls (x1, xi) n =
    (fmul x1 n, fmul xi n)
End

val () = cv_trans f2muls_def;

Definition f2sqr_def:
  f2sqr (x1,xi) = let
    a = fadd x1 xi;
    b = fsub x1 xi;
    c = fadd x1 x1;
  in (fmul a b, fmul c xi)
End

val () = cv_trans f2sqr_def;

Definition f2sub_def:
  f2sub (x1,xi) (y1,yi) =
    (fsub x1 y1, fsub xi yi)
End

val () = cv_trans f2sub_def;

Definition fneg_def:
  fneg x = bn254p - x
End

val () = cv_trans fneg_def;

Definition f2neg_def:
  f2neg (x1,xi) =
    (fneg x1, fneg xi)
End

val () = cv_trans f2neg_def;

Definition f2one_def:
  f2one = (1n, 0n)
End

val () = cv_trans_deep_embedding EVAL f2one_def;

Definition f2inv_def:
  f2inv (x1, xi) = let
    fr = finv (fadd (fmul x1 x1) (fmul xi xi));
  in (fmul fr x1, fmul fr (fneg xi))
End

val () = cv_trans f2inv_def;

Definition f2div_def:
  f2div x y =
  f2mul x (f2inv y)
End

val () = cv_trans f2div_def;

Definition f2div2_def:
  f2div2 = f2div f2one (f2muls f2one 2)
End

val () = cv_trans_deep_embedding EVAL f2div2_def;

Definition dbl6_def:
  dbl6 (x, (y, z)) = let
    t0 = f2sqr y;
    t1 = f2sqr z;
    t2 = f2mul (f2muls t1 3) bn254bF2;
    t3 = f2muls t2 3;
    t4 = f2sub (f2sub (f2sqr (f2add y z)) t1) t0;
    c0 = f2sub t2 t0;
    c1 = f2muls (f2sqr x) 3;
    c2 = f2neg t4;
    rx = f2mul (f2mul (f2mul (f2sub t0 t3) x) y) f2div2;
    ry = f2sub (f2sqr (f2mul (f2add t0 t3) f2div2)) (f2muls (f2sqr t2) 3);
    rz = f2mul t0 t4
  in (rx, (ry, rz))
End

val () = cv_trans dbl6_def;

Definition dbl6_line_def:
  dbl6_line (x, (y, z)) = let
    t0 = f2sqr y;
    t1 = f2sqr z;
    t2 = f2mul (f2muls t1 3) bn254bF2;
    t3 = f2muls t2 3;
    t4 = f2sub (f2sub (f2sqr (f2add y z)) t1) t0;
    c0 = f2sub t2 t0;
    c1 = f2muls (f2sqr x) 3;
    c2 = f2neg t4;
    rx = f2mul (f2mul (f2mul (f2sub t0 t3) x) y) f2div2;
    ry = f2sub (f2sqr (f2mul (f2add t0 t3) f2div2)) (f2muls (f2sqr t2) 3);
    rz = f2mul t0 t4
  in ((rx, (ry, rz)), (c0, (c1, c2)))
End

val () = cv_trans dbl6_line_def;

Definition add6_def:
  add6 (rx, (ry, rz)) (qx,qy) = let
    t0 = f2sub ry (f2mul qy rz);
    t1 = f2sub rx (f2mul qx rz);
    c0 = f2sub (f2mul t0 qx) (f2mul t1 qy);
    c1 = f2neg t0;
    c2 = t1;
    t2 = f2sqr t1;
    t3 = f2mul t2 t1;
    t4 = f2mul t2 rx;
    t5 = f2add (f2sub t3 (f2muls t4 2))
               (f2mul (f2sqr t0) rz);
    rx = f2mul t1 t5;
    ry = f2sub (f2mul (f2sub t4 t5) t0)
               (f2mul t3 ry);
    rz = f2mul rz t3;
  in (rx, (ry, rz))
End

val () = cv_trans add6_def;

Definition add6_line_def:
  add6_line (rx, (ry, rz)) (qx,qy) = let
    t0 = f2sub ry (f2mul qy rz);
    t1 = f2sub rx (f2mul qx rz);
    c0 = f2sub (f2mul t0 qx) (f2mul t1 qy);
    c1 = f2neg t0;
    c2 = t1;
    t2 = f2sqr t1;
    t3 = f2mul t2 t1;
    t4 = f2mul t2 rx;
    t5 = f2add (f2sub t3 (f2muls t4 2))
               (f2mul (f2sqr t0) rz);
    rx' = f2mul t1 t5;
    ry' = f2sub (f2mul (f2sub t4 t5) t0)
               (f2mul t3 ry);
    rz' = f2mul rz t3;
  in ((rx', (ry', rz')), (c0, (c1, c2)))
End

val () = cv_trans add6_line_def;

Definition f2_nonresidue_def:
  f2_nonresidue = (9n, 1n)
End

val () = cv_trans_deep_embedding EVAL f2_nonresidue_def;

(* Polynomial FQ12 - direct 12-coefficient representation matching py_ecc *)
(* Modulus: w^12 = 18*w^6 - 82 *)

Definition poly12_zero_def:
  poly12_zero = (0n,0n,0n,0n,0n,0n,0n,0n,0n,0n,0n,0n)
End

val () = cv_trans_deep_embedding EVAL poly12_zero_def;

Definition poly12_one_def:
  poly12_one = (1n,0n,0n,0n,0n,0n,0n,0n,0n,0n,0n,0n)
End

val () = cv_trans_deep_embedding EVAL poly12_one_def;

Definition poly12_add_def:
  poly12_add (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11)
             (b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11) =
    (fadd a0 b0, fadd a1 b1, fadd a2 b2, fadd a3 b3,
     fadd a4 b4, fadd a5 b5, fadd a6 b6, fadd a7 b7,
     fadd a8 b8, fadd a9 b9, fadd a10 b10, fadd a11 b11)
End

val () = cv_trans poly12_add_def;

Definition poly12_sub_def:
  poly12_sub (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11)
             (b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11) =
    (fsub a0 b0, fsub a1 b1, fsub a2 b2, fsub a3 b3,
     fsub a4 b4, fsub a5 b5, fsub a6 b6, fsub a7 b7,
     fsub a8 b8, fsub a9 b9, fsub a10 b10, fsub a11 b11)
End

val () = cv_trans poly12_sub_def;

Definition poly12_neg_def:
  poly12_neg (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11) =
    (fneg a0, fneg a1, fneg a2, fneg a3,
     fneg a4, fneg a5, fneg a6, fneg a7,
     fneg a8, fneg a9, fneg a10, fneg a11)
End

val () = cv_trans poly12_neg_def;

(* Multiply and reduce by w^12 = 18*w^6 - 82 *)
(* After convolution we have 23 coefficients (indices 0-22) *)
(* Reduce from top: c[i+12] contributes -82*c[i+12] to c[i] and 18*c[i+12] to c[i+6] *)
Definition poly12_mul_def:
  poly12_mul (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11)
             (b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11) = let
    (* Convolution: c[k] = sum_{i+j=k} a[i]*b[j] *)
    c0 = fmul a0 b0;
    c1 = fadd (fmul a0 b1) (fmul a1 b0);
    c2 = fadd (fadd (fmul a0 b2) (fmul a1 b1)) (fmul a2 b0);
    c3 = fadd (fadd (fadd (fmul a0 b3) (fmul a1 b2)) (fmul a2 b1)) (fmul a3 b0);
    c4 = fadd (fadd (fadd (fadd (fmul a0 b4) (fmul a1 b3)) (fmul a2 b2)) (fmul a3 b1)) (fmul a4 b0);
    c5 = fadd (fadd (fadd (fadd (fadd (fmul a0 b5) (fmul a1 b4)) (fmul a2 b3)) (fmul a3 b2)) (fmul a4 b1)) (fmul a5 b0);
    c6 = fadd (fadd (fadd (fadd (fadd (fadd (fmul a0 b6) (fmul a1 b5)) (fmul a2 b4)) (fmul a3 b3)) (fmul a4 b2)) (fmul a5 b1)) (fmul a6 b0);
    c7 = fadd (fadd (fadd (fadd (fadd (fadd (fmul a0 b7) (fmul a1 b6)) (fmul a2 b5)) (fmul a3 b4)) (fmul a4 b3)) (fmul a5 b2)) (fadd (fmul a6 b1) (fmul a7 b0));
    c8 = fadd (fadd (fadd (fadd (fadd (fadd (fmul a0 b8) (fmul a1 b7)) (fmul a2 b6)) (fmul a3 b5)) (fmul a4 b4)) (fmul a5 b3)) (fadd (fadd (fmul a6 b2) (fmul a7 b1)) (fmul a8 b0));
    c9 = fadd (fadd (fadd (fadd (fadd (fadd (fmul a0 b9) (fmul a1 b8)) (fmul a2 b7)) (fmul a3 b6)) (fmul a4 b5)) (fmul a5 b4)) (fadd (fadd (fadd (fmul a6 b3) (fmul a7 b2)) (fmul a8 b1)) (fmul a9 b0));
    c10 = fadd (fadd (fadd (fadd (fadd (fadd (fmul a0 b10) (fmul a1 b9)) (fmul a2 b8)) (fmul a3 b7)) (fmul a4 b6)) (fmul a5 b5)) (fadd (fadd (fadd (fadd (fmul a6 b4) (fmul a7 b3)) (fmul a8 b2)) (fmul a9 b1)) (fmul a10 b0));
    c11 = fadd (fadd (fadd (fadd (fadd (fadd (fmul a0 b11) (fmul a1 b10)) (fmul a2 b9)) (fmul a3 b8)) (fmul a4 b7)) (fmul a5 b6)) (fadd (fadd (fadd (fadd (fadd (fmul a6 b5) (fmul a7 b4)) (fmul a8 b3)) (fmul a9 b2)) (fmul a10 b1)) (fmul a11 b0));
    c12 = fadd (fadd (fadd (fadd (fadd (fadd (fmul a1 b11) (fmul a2 b10)) (fmul a3 b9)) (fmul a4 b8)) (fmul a5 b7)) (fmul a6 b6)) (fadd (fadd (fadd (fadd (fmul a7 b5) (fmul a8 b4)) (fmul a9 b3)) (fmul a10 b2)) (fmul a11 b1));
    c13 = fadd (fadd (fadd (fadd (fadd (fmul a2 b11) (fmul a3 b10)) (fmul a4 b9)) (fmul a5 b8)) (fmul a6 b7)) (fadd (fadd (fadd (fadd (fmul a7 b6) (fmul a8 b5)) (fmul a9 b4)) (fmul a10 b3)) (fmul a11 b2));
    c14 = fadd (fadd (fadd (fadd (fmul a3 b11) (fmul a4 b10)) (fmul a5 b9)) (fmul a6 b8)) (fadd (fadd (fadd (fadd (fmul a7 b7) (fmul a8 b6)) (fmul a9 b5)) (fmul a10 b4)) (fmul a11 b3));
    c15 = fadd (fadd (fadd (fmul a4 b11) (fmul a5 b10)) (fmul a6 b9)) (fadd (fadd (fadd (fadd (fmul a7 b8) (fmul a8 b7)) (fmul a9 b6)) (fmul a10 b5)) (fmul a11 b4));
    c16 = fadd (fadd (fmul a5 b11) (fmul a6 b10)) (fadd (fadd (fadd (fadd (fmul a7 b9) (fmul a8 b8)) (fmul a9 b7)) (fmul a10 b6)) (fmul a11 b5));
    c17 = fadd (fmul a6 b11) (fadd (fadd (fadd (fadd (fmul a7 b10) (fmul a8 b9)) (fmul a9 b8)) (fmul a10 b7)) (fmul a11 b6));
    c18 = fadd (fadd (fadd (fadd (fmul a7 b11) (fmul a8 b10)) (fmul a9 b9)) (fmul a10 b8)) (fmul a11 b7);
    c19 = fadd (fadd (fadd (fmul a8 b11) (fmul a9 b10)) (fmul a10 b9)) (fmul a11 b8);
    c20 = fadd (fadd (fmul a9 b11) (fmul a10 b10)) (fmul a11 b9);
    c21 = fadd (fmul a10 b11) (fmul a11 b10);
    c22 = fmul a11 b11;
    (* Reduce: w^12 = 18*w^6 - 82 *)
    (* Process from c22 down to c12 *)
    (* c22 at position 22: subtract 82*c22 from c10, add 18*c22 to c16 *)
    c10 = fsub c10 (fmul 82n c22);
    c16 = fadd c16 (fmul 18n c22);
    (* c21 -> c9, c15 *)
    c9 = fsub c9 (fmul 82n c21);
    c15 = fadd c15 (fmul 18n c21);
    (* c20 -> c8, c14 *)
    c8 = fsub c8 (fmul 82n c20);
    c14 = fadd c14 (fmul 18n c20);
    (* c19 -> c7, c13 *)
    c7 = fsub c7 (fmul 82n c19);
    c13 = fadd c13 (fmul 18n c19);
    (* c18 -> c6, c12 *)
    c6 = fsub c6 (fmul 82n c18);
    c12 = fadd c12 (fmul 18n c18);
    (* c17 -> c5, c11 *)
    c5 = fsub c5 (fmul 82n c17);
    c11 = fadd c11 (fmul 18n c17);
    (* c16 -> c4, c10 *)
    c4 = fsub c4 (fmul 82n c16);
    c10 = fadd c10 (fmul 18n c16);
    (* c15 -> c3, c9 *)
    c3 = fsub c3 (fmul 82n c15);
    c9 = fadd c9 (fmul 18n c15);
    (* c14 -> c2, c8 *)
    c2 = fsub c2 (fmul 82n c14);
    c8 = fadd c8 (fmul 18n c14);
    (* c13 -> c1, c7 *)
    c1 = fsub c1 (fmul 82n c13);
    c7 = fadd c7 (fmul 18n c13);
    (* c12 -> c0, c6 *)
    c0 = fsub c0 (fmul 82n c12);
    c6 = fadd c6 (fmul 18n c12)
  in (c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11)
End

val () = cv_trans poly12_mul_def;

Definition poly12_sqr_def:
  poly12_sqr a = poly12_mul a a
End

val () = cv_trans poly12_sqr_def;

(* Scalar multiplication *)
Definition poly12_scale_def:
  poly12_scale s (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11) =
    (fmul s a0, fmul s a1, fmul s a2, fmul s a3,
     fmul s a4, fmul s a5, fmul s a6, fmul s a7,
     fmul s a8, fmul s a9, fmul s a10, fmul s a11)
End

val () = cv_trans poly12_scale_def;

(* Conjugation: negate coefficients 1,3,5,7,9,11 (the odd positions) *)
(* This corresponds to w -> -w *)
Definition poly12_conj_def:
  poly12_conj (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11) =
    (a0, fneg a1, a2, fneg a3, a4, fneg a5,
     a6, fneg a7, a8, fneg a9, a10, fneg a11)
End

val () = cv_trans poly12_conj_def;

(* Conversion between poly12 and tower representation *)
(* Tower: ((a0,(a1,a2)),(b0,(b1,b2))) where each ai,bi is FQ2 = (real,imag) *)
(* Poly12: (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11) *)
(* Mapping: a0 -> (c0,c6), a1 -> (c2,c8), a2 -> (c4,c10) *)
(*          b0 -> (c1,c7), b1 -> (c3,c9), b2 -> (c5,c11) *)

Definition poly12_to_tower_def:
  poly12_to_tower (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11) =
    ((((c0,c6), ((c2,c8), (c4,c10))),
      ((c1,c7), ((c3,c9), (c5,c11)))))
      : (((num # num) # (num # num) # num # num) #
         (num # num) # (num # num) # num # num)
End

val () = cv_trans poly12_to_tower_def;

Definition tower_to_poly12_def:
  tower_to_poly12 (((a0r,a0i), ((a1r,a1i), (a2r,a2i))),
                   ((b0r,b0i), ((b1r,b1i), (b2r,b2i)))) =
    (a0r, b0r, a1r, b1r, a2r, b2r,
     a0i, b0i, a1i, b1i, a2i, b2i)
End

val () = cv_trans tower_to_poly12_def;

Definition f6mul01_def:
  f6mul01 (c0, (c1, c2)) b0 b1 = let
    t0 = f2mul c0 b0;
    t1 = f2mul c1 b1;
  in (
    f2add (f2mul (f2sub (f2mul (f2add c1 c2) b1) t1) f2_nonresidue) t0,
    (f2sub (f2sub (f2mul (f2add b0 b1) (f2add c0 c1)) t0) t1,
     f2add (f2sub (f2mul (f2add c0 c2) b0) t0) t1)
  )
End

val () = cv_trans f6mul01_def;

Definition f6add_def:
  f6add (c0, (c1, c2)) (r0, (r1, r2)) =
    (f2add c0 r0,
     (f2add c1 r1,
      f2add c2 r2))
End

val () = cv_trans f6add_def;

Definition f6sub_def:
  f6sub (c0, (c1, c2)) (r0, (r1, r2)) =
    (f2sub c0 r0,
     (f2sub c1 r1,
      f2sub c2 r2))
End

val () = cv_trans f6sub_def;

Definition f6mul_def:
  f6mul (c0, (c1, c2)) (r0, (r1, r2)) = let
    t0 = f2mul c0 r0;
    t1 = f2mul c1 r1;
    t2 = f2mul c2 r2;
  in (
    f2add t0 (f2mul (f2sub (f2mul (f2add c1 c2) (f2add r1 r2)) (f2add t1 t2))
              f2_nonresidue),
    (f2add (f2sub (f2mul (f2add c0 c1) (f2add r0 r1)) (f2add t0 t1))
          (f2mul t2 f2_nonresidue),
     f2sub (f2add t1 (f2mul (f2add c0 c2) (f2add r0 r2)))
          (f2add t0 t2))
    )
End

val () = cv_trans f6mul_def;

Definition f6sqr_def:
  f6sqr (c0, (c1, c2)) = let
    s0 = f2sqr c0;
    ab = f2mul c0 c1;
    s1 = f2add ab ab;
    s2 = f2sqr (f2sub (f2add c0 c2) c1);
    bc = f2mul c1 c2;
    s3 = f2add bc bc;
    s4 = f2sqr c2;
  in (
    f2add s0 (f2mul s3 f2_nonresidue),
    (f2add s1 (f2mul s4 f2_nonresidue),
     f2sub (f2add (f2add s1 s2) s3) (f2add s0 s4))
  )
End

val () = cv_trans f6sqr_def;

Definition f6neg_def:
  f6neg (c0, (c1, c2)) = (f2neg c0, (f2neg c1, f2neg c2))
End

val () = cv_trans f6neg_def;

Definition f6mul_nonresidue_def:
  f6mul_nonresidue (c0, (c1, c2)) =
    (f2mul c2 f2_nonresidue, (c0, c1))
End

val () = cv_trans f6mul_nonresidue_def;

Definition f12mul034_def:
  f12mul034 (c0,c1) o0 o3 o4 = let
    a = (f2mul (FST c0) o0,
         (f2mul (FST (SND c0)) o0,
          f2mul (SND (SND c0)) o0));
    b = f6mul01 c1 o3 o4;
    e = f6mul01 (f6add c0 c1) (f2add o0 o3) o4;
  in (f6add (f6mul_nonresidue b) a,
      f6sub e (f6add a b))
End

val () = cv_trans f12mul034_def;

Definition lineFunction_def:
  lineFunction c0 c1 c2 f px py =
  f12mul034 f (f2muls c2 py) (f2muls c1 px) c0
End

val () = cv_trans lineFunction_def;

Definition weierstrassEquationF2_def:
  weierstrassEquationF2 x = let
    x2 = f2mul x x;
    x3 = f2mul x2 x
  in f2add x3 bn254bF2
End

val () = cv_trans weierstrassEquationF2_def;

Definition validAffineF2_def:
  validAffineF2 ((x1,xi),(y1,yi)) =
    (x1 < bn254p ∧ xi < bn254p ∧
     y1 < bn254p ∧ yi < bn254p ∧
     (((x1,xi) = (0,0) ∧ (y1,yi) = (0,0)) ∨
      f2mul (y1,yi) (y1,yi) =
      weierstrassEquationF2 (x1,xi)))
End

val () = cv_trans validAffineF2_def;

Definition f2zero_def:
  f2zero = (0n, 0n)
End

val () = cv_trans_deep_embedding EVAL f2zero_def;

Definition zeroF2_def:
  zeroF2 = (f2zero, (f2one, f2zero))
End

val () = cv_trans_deep_embedding EVAL zeroF2_def;

Definition fromAffineF2_def:
  fromAffineF2 (x, y) =
  if (x, y) = (f2zero, f2zero) then zeroF2 else (x, (y, f2one))
End

val () = cv_trans fromAffineF2_def;

Definition toAffineF2_def:
  toAffineF2 (x, (y, z)) =
  if z = f2one then (x, y) else
  if z = f2zero then (f2zero, f2zero) else
  let iz = f2inv z in
    (f2mul x iz, f2mul y iz)
End

val () = cv_trans toAffineF2_def;

Definition dblF2_def:
  dblF2 (x, (y, z)) = let
    a = f2sqr x;
    b = f2sqr y;
    c = f2sqr b;
    d = f2sub (f2sqr (f2add x b)) (f2add a c);
    d = f2add d d;
    e = f2add (f2add a a) a;
    f = f2sqr e;
    rx = f2sub f (f2add d d);
    ry = f2sub (f2mul e (f2sub d rx)) (f2add (f2add (f2add c c) c) (f2add (f2add c c) c));
    rz = f2mul (f2add y y) z
  in (rx, (ry, rz))
End

val () = cv_trans dblF2_def;

Definition addF2_def:
  addF2 (x1, (y1, z1)) (x2,y2) = let
    z1z1 = f2sqr z1;
    u2 = f2mul x2 z1z1;
    s2 = f2mul (f2mul y2 z1) z1z1;
    h = f2sub u2 x1;
    hh = f2sqr h;
    i = f2add hh hh; i = f2add i i;
    j = f2mul h i;
    r = f2sub s2 y1; r = f2add r r;
    v = f2mul x1 i;
    rx = f2sub (f2sub (f2sqr r) j) (f2add v v);
    ry = f2sub (f2mul r (f2sub v rx)) (f2mul (f2add y1 y1) j);
    rz = f2sub (f2sqr (f2add z1 h)) (f2add z1z1 hh)
  in (rx, (ry, rz))
End

val () = cv_trans addF2_def;

Definition mulF2_loop_def:
  mulF2_loop a p n =
  if n = 0 then a
  else let
    a = if ODD n then addF2 a (FST p, FST (SND p)) else a;
    p = dblF2 p;
    n = n DIV 2
  in mulF2_loop a p n
End

val () = cv_trans mulF2_loop_def;

Definition mulF2_def:
  mulF2 p n =
  if n = 0 then zeroF2 else
  if SND(SND p) = f2zero ∨ n = 1 then p else
    mulF2_loop zeroF2 p (n MOD bn254n)
End

val () = cv_trans mulF2_def;

Definition mulAffineF2_def:
  mulAffineF2 p n =
  toAffineF2 (mulF2 (fromAffineF2 p) n)
End

val () = cv_trans mulAffineF2_def;

Definition mulFQ12_def:
  mulFQ12 (a0, a1) (b0, b1) = let
    t0 = f6mul a0 b0;
    t1 = f6mul a1 b1;
    c0 = f6add t0 (f6mul_nonresidue t1);
    c1 = f6sub (f6mul (f6add a0 a1) (f6add b0 b1)) (f6add t0 t1)
  in (c0, c1)
End

val () = cv_trans mulFQ12_def;

Definition f12sqr_def:
  f12sqr (c0, c1) = let
    ab = f6mul c0 c1;
    c0' = f6mul (f6add c0 c1)
                (f6add c0 (f6mul_nonresidue c1));
    c0' = f6sub (f6sub c0' ab) (f6mul_nonresidue ab);
    c1' = f6add ab ab
  in (c0', c1')
End

val () = cv_trans f12sqr_def;

Definition f12conj_def:
  f12conj (c0, c1) = (c0, f6neg c1)
End

val () = cv_trans f12conj_def;

Definition f6inv_def:
  f6inv (c0, (c1, c2)) = let
    t0 = f2sqr c0;
    t1 = f2sqr c1;
    t2 = f2sqr c2;
    t3 = f2mul c0 c1;
    t4 = f2mul c0 c2;
    t5 = f2mul c1 c2;
    c0' = f2sub t0 (f2mul t5 f2_nonresidue);
    c1' = f2sub (f2mul t2 f2_nonresidue) t3;
    c2' = f2sub t1 t4;
    t6 = f2mul c0 c0';
    t6 = f2add t6 (f2mul c1 (f2mul c2' f2_nonresidue));
    t6 = f2add t6 (f2mul c2 (f2mul c1' f2_nonresidue));
    t6 = f2inv t6
  in (f2mul c0' t6, (f2mul c1' t6, f2mul c2' t6))
End

val () = cv_trans f6inv_def;

Definition f12inv_def:
  f12inv (c0, c1) = let
    t0 = f6sqr c0;
    t1 = f6sqr c1;
    t0 = f6sub t0 (f6mul_nonresidue t1);
    t1 = f6inv t0
  in (f6mul c0 t1, f6neg (f6mul c1 t1))
End

val () = cv_trans f12inv_def;

(* Polynomial FQ12 inverse using extended Euclidean algorithm *)
(* Uses 13-tuples (degree 12 polynomials with indices 0-12) *)

(* Find degree of polynomial (index of highest non-zero coeff) *)
Definition poly13_deg_def:
  poly13_deg (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12) : num =
    if c12 ≠ 0n then 12n else
    if c11 ≠ 0n then 11n else
    if c10 ≠ 0n then 10n else
    if c9 ≠ 0n then 9n else
    if c8 ≠ 0n then 8n else
    if c7 ≠ 0n then 7n else
    if c6 ≠ 0n then 6n else
    if c5 ≠ 0n then 5n else
    if c4 ≠ 0n then 4n else
    if c3 ≠ 0n then 3n else
    if c2 ≠ 0n then 2n else
    if c1 ≠ 0n then 1n else 0n
End

val () = cv_trans poly13_deg_def;

(* Get coefficient at index *)
Definition poly13_get_def:
  poly13_get (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12) (i:num) =
    if i = 0n then c0 else
    if i = 1n then c1 else
    if i = 2n then c2 else
    if i = 3n then c3 else
    if i = 4n then c4 else
    if i = 5n then c5 else
    if i = 6n then c6 else
    if i = 7n then c7 else
    if i = 8n then c8 else
    if i = 9n then c9 else
    if i = 10n then c10 else
    if i = 11n then c11 else c12
End

val () = cv_trans poly13_get_def;

(* Set coefficient at index *)
Definition poly13_set_def:
  poly13_set (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12) (i:num) v =
    (if i = 0n then v else c0,
     if i = 1n then v else c1,
     if i = 2n then v else c2,
     if i = 3n then v else c3,
     if i = 4n then v else c4,
     if i = 5n then v else c5,
     if i = 6n then v else c6,
     if i = 7n then v else c7,
     if i = 8n then v else c8,
     if i = 9n then v else c9,
     if i = 10n then v else c10,
     if i = 11n then v else c11,
     if i = 12n then v else c12)
End

val () = cv_trans poly13_set_def;

Definition poly13_zero_def:
  poly13_zero = (0n,0n,0n,0n,0n,0n,0n,0n,0n,0n,0n,0n,0n)
End

val () = cv_trans_deep_embedding EVAL poly13_zero_def;

(* Add two 13-tuples *)
Definition poly13_add_def:
  poly13_add (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12)
             (b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12) =
    (fadd a0 b0, fadd a1 b1, fadd a2 b2, fadd a3 b3,
     fadd a4 b4, fadd a5 b5, fadd a6 b6, fadd a7 b7,
     fadd a8 b8, fadd a9 b9, fadd a10 b10, fadd a11 b11, fadd a12 b12)
End

val () = cv_trans poly13_add_def;

(* Subtract two 13-tuples *)
Definition poly13_sub_def:
  poly13_sub (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12)
             (b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12) =
    (fsub a0 b0, fsub a1 b1, fsub a2 b2, fsub a3 b3,
     fsub a4 b4, fsub a5 b5, fsub a6 b6, fsub a7 b7,
     fsub a8 b8, fsub a9 b9, fsub a10 b10, fsub a11 b11, fsub a12 b12)
End

val () = cv_trans poly13_sub_def;

(* Scale a 13-tuple by a scalar *)
Definition poly13_scale_def:
  poly13_scale s (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12) =
    (fmul s a0, fmul s a1, fmul s a2, fmul s a3,
     fmul s a4, fmul s a5, fmul s a6, fmul s a7,
     fmul s a8, fmul s a9, fmul s a10, fmul s a11, fmul s a12)
End

val () = cv_trans poly13_scale_def;

(* Inner loop of poly_rounded_div: subtract o[i]*b shifted by i from temp *)
Definition poly_div_inner_def:
  poly_div_inner temp o_i b degb i c =
    if c > degb then temp
    else let
      idx = c + i;
      temp' = poly13_set temp idx (fsub (poly13_get temp idx) (fmul o_i (poly13_get b c)))
    in poly_div_inner temp' o_i b degb i (c + 1)
Termination
  WF_REL_TAC `measure (λ(temp,o_i,b,degb,i,c). degb + 1 - c)`
End

val () = cv_trans poly_div_inner_def;

(* Outer loop of poly_rounded_div - counts down from start to 0 *)
Definition poly_div_outer_def:
  poly_div_outer temp o_out b degb i =
    let
      q = fdiv (poly13_get temp (degb + i)) (poly13_get b degb);
      o_out' = poly13_set o_out i (fadd (poly13_get o_out i) q);
      temp' = poly_div_inner temp q b degb i 0n
    in if i = 0n then (temp', o_out')
       else poly_div_outer temp' o_out' b degb (i - 1n)
Termination
  WF_REL_TAC `measure (λ(temp,o_out,b,degb,i). i)`
End

val () = cv_trans poly_div_outer_def;

(* Polynomial divmod: returns (remainder, quotient) *)
Definition poly13_divmod_def:
  poly13_divmod a b = let
    dega = poly13_deg a;
    degb = poly13_deg b
  in if dega < degb then (a, poly13_zero)
     else poly_div_outer a poly13_zero b degb (dega - degb)
End

val () = cv_trans poly13_divmod_def;

(* Polynomial rounded division: a / b *)
Definition poly13_div_def:
  poly13_div a b = SND (poly13_divmod a b)
End

val () = cv_trans poly13_div_def;

(* Polynomial remainder: a mod b *)
Definition poly13_mod_def:
  poly13_mod a b = FST (poly13_divmod a b)
End

val () = cv_trans poly13_mod_def;

(* Inner loop for inverse: update nm and new *)
Definition inv_inner_j_def:
  inv_inner_j nm new lm low r i j =
    if j + i > 12 then (nm, new)
    else let
      r_j = poly13_get r j;
      nm' = poly13_set nm (i + j) (fsub (poly13_get nm (i + j)) (fmul (poly13_get lm i) r_j));
      new' = poly13_set new (i + j) (fsub (poly13_get new (i + j)) (fmul (poly13_get low i) r_j))
    in inv_inner_j nm' new' lm low r i (j + 1)
Termination
  WF_REL_TAC `measure (λ(nm,new,lm,low,r,i,j). 13 - j)`
End

val () = cv_trans inv_inner_j_def;

Definition inv_inner_i_def:
  inv_inner_i nm new lm low r i =
    if i > 12 then (nm, new)
    else let
      (nm', new') = inv_inner_j nm new lm low r i 0
    in inv_inner_i nm' new' lm low r (i + 1)
Termination
  WF_REL_TAC `measure (λ(nm,new,lm,low,r,i). 13 - i)`
End

val () = cv_trans inv_inner_i_def;

(* Main inverse loop *)
Definition poly12_inv_loop_def:
  poly12_inv_loop lm hm low high =
    if poly13_deg low = 0 then (lm, low)
    else let
      r = poly13_div high low;
      (nm, new) = inv_inner_i hm high lm low r 0
    in poly12_inv_loop nm lm new low
Termination
  WF_REL_TAC `measure (λ(lm,hm,low,high). poly13_deg low)`
  \\ rw [] \\ cheat
End

val () = cv_trans poly12_inv_loop_def;

(* The FQ12 modulus coefficients: w^12 - 18*w^6 + 82 = 0 *)
(* So modulus_coeffs = (82, 0, 0, 0, 0, 0, -18, 0, 0, 0, 0, 0, 1) *)
(* But we use positive field elements, so -18 = p - 18 *)
Definition poly12_modulus_def:
  poly12_modulus = (82n, 0n, 0n, 0n, 0n, 0n,
                    21888242871839275222246405745257275088696311157297823662689037894645226208565n,
                    0n, 0n, 0n, 0n, 0n, 1n)
End

val () = cv_trans_deep_embedding EVAL poly12_modulus_def;

(* Convert poly12 to poly13 by appending 0 *)
Definition poly12_to_poly13_def:
  poly12_to_poly13 (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11) =
    (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,0n)
End

val () = cv_trans poly12_to_poly13_def;

(* Convert poly13 to poly12 by dropping last *)
Definition poly13_to_poly12_def:
  poly13_to_poly12 (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12) =
    (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11)
End

val () = cv_trans poly13_to_poly12_def;

(* Complete poly12 inverse *)
Definition poly12_inv_def:
  poly12_inv p = let
    lm = (1n,0n,0n,0n,0n,0n,0n,0n,0n,0n,0n,0n,0n);
    hm = poly13_zero;
    low = poly12_to_poly13 p;
    high = poly12_modulus;
    (result_lm, result_low) = poly12_inv_loop lm hm low high;
    inv_coeff = finv (poly13_get result_low 0)
  in poly13_to_poly12 (poly13_scale inv_coeff result_lm)
End

val () = cv_trans poly12_inv_def;

Definition poly12_div_def:
  poly12_div a b = poly12_mul a (poly12_inv b)
End

val () = cv_trans poly12_div_def;

(* Poly12 twist: place FQ2 element at appropriate position *)
(* For x: positions (2, 8) - corresponds to w^2 coefficient *)
(* For y: positions (3, 9) - corresponds to w^3 coefficient *)
Definition poly12_twist_x_def:
  poly12_twist_x (a, b) = let
    c0 = fsub a (fmul 9n b);
    c1 = b
  in (0n, 0n, c0, 0n, 0n, 0n, 0n, 0n, c1, 0n, 0n, 0n)
End

val () = cv_trans poly12_twist_x_def;

Definition poly12_twist_y_def:
  poly12_twist_y (a, b) = let
    c0 = fsub a (fmul 9n b);
    c1 = b
  in (0n, 0n, 0n, c0, 0n, 0n, 0n, 0n, 0n, c1, 0n, 0n)
End

val () = cv_trans poly12_twist_y_def;

(* Embed FQ element at position 0 *)
Definition poly12_embed_fq_def:
  poly12_embed_fq x = (x, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n)
End

val () = cv_trans poly12_embed_fq_def;

(* Poly12 point doubling *)
Definition poly12_double_def:
  poly12_double (x1, y1) = let
    m = poly12_div (poly12_mul (poly12_embed_fq 3n) (poly12_sqr x1))
                   (poly12_add y1 y1);
    x3 = poly12_sub (poly12_sqr m) (poly12_add x1 x1);
    y3 = poly12_sub (poly12_mul m (poly12_sub x1 x3)) y1
  in (x3, y3)
End

val () = cv_trans poly12_double_def;

(* Poly12 point addition *)
Definition poly12_point_add_def:
  poly12_point_add (x1, y1) (x2, y2) =
  if x1 = x2 then
    if y1 = y2 then poly12_double (x1, y1)
    else (poly12_zero, poly12_zero)
  else let
    m = poly12_div (poly12_sub y2 y1) (poly12_sub x2 x1);
    x3 = poly12_sub (poly12_sub (poly12_sqr m) x1) x2;
    y3 = poly12_sub (poly12_mul m (poly12_sub x1 x3)) y1
  in (x3, y3)
End

val () = cv_trans poly12_point_add_def;

(* Line function for pairing *)
Definition poly12_linefunc_def:
  poly12_linefunc (x1, y1) (x2, y2) (xt, yt) =
  if x1 = x2 then
    if y1 = y2 then
      let m = poly12_div (poly12_mul (poly12_embed_fq 3n) (poly12_sqr x1))
                         (poly12_add y1 y1)
      in poly12_sub (poly12_mul m (poly12_sub xt x1)) (poly12_sub yt y1)
    else poly12_sub xt x1
  else
    let m = poly12_div (poly12_sub y2 y1) (poly12_sub x2 x1)
    in poly12_sub (poly12_mul m (poly12_sub xt x1)) (poly12_sub yt y1)
End

val () = cv_trans poly12_linefunc_def;

Definition f12add_def:
  f12add (a0, a1) (b0, b1) = (f6add a0 b0, f6add a1 b1)
End

val () = cv_trans f12add_def;

Definition f12sub_def:
  f12sub (a0, a1) (b0, b1) = (f6sub a0 b0, f6sub a1 b1)
End

val () = cv_trans f12sub_def;

Definition f12div_def:
  f12div a b = mulFQ12 a (f12inv b)
End

val () = cv_trans f12div_def;

Definition fq12zero_def:
  fq12zero =
  (((0n,0n), ((0n,0n), (0n,0n))),
   ((0n,0n), ((0n,0n), (0n,0n))))
End

val () = cv_trans_deep_embedding EVAL fq12zero_def;

Definition fq12one_def:
  fq12one =
  (((1n,0n), ((0n,0n), (0n,0n))),
   ((0n,0n), ((0n,0n), (0n,0n))))
End

val () = cv_trans_deep_embedding EVAL fq12one_def;

(* Embed FQ2 element into FQ12 at specific positions for twist *)
(* py_ecc twist: (a,b) -> (a-9b, b) then multiply by w^2 or w^3 *)
(* For x: embed at position w^2 = V (a1 in fq6_low) *)
(* For y: embed at position w^3 = W*V (b1 in fq6_high) *)
Definition twist_x_def:
  twist_x (a, b) = let
    (* Isomorphism: (a, b) -> (a - 9*b, b) *)
    c0 = fsub a (fmul 9n b);
    c1 = b
  in
    (* Place at position a1 in fq6_low *)
    (((0n,0n), ((c0, c1), (0n,0n))),
     ((0n,0n), ((0n,0n), (0n,0n))))
End

val () = cv_trans twist_x_def;

Definition twist_y_def:
  twist_y (a, b) = let
    c0 = fsub a (fmul 9n b);
    c1 = b
  in
    (* Place at position b1 in fq6_high *)
    (((0n,0n), ((0n,0n), (0n,0n))),
     ((0n,0n), ((c0, c1), (0n,0n))))
End

val () = cv_trans twist_y_def;

(* Embed FQ element into FQ12 at position 0 (for P coordinates) *)
Definition embed_fq_def:
  embed_fq x =
    (((x, 0n), ((0n,0n), (0n,0n))),
     ((0n,0n), ((0n,0n), (0n,0n))))
End

val () = cv_trans embed_fq_def;

(* FQ12 point doubling (affine coordinates) *)
Definition f12_double_def:
  f12_double (x1, y1) = let
    m = f12div (mulFQ12 (embed_fq 3n) (f12sqr x1))
               (f12add y1 y1);
    x3 = f12sub (f12sqr m) (f12add x1 x1);
    y3 = f12sub (mulFQ12 m (f12sub x1 x3)) y1
  in (x3, y3)
End

val () = cv_trans f12_double_def;

(* FQ12 point addition (affine coordinates) *)
Definition f12_add_def:
  f12_add (x1, y1) (x2, y2) =
  if x1 = x2 then
    if y1 = y2 then f12_double (x1, y1)
    else (fq12zero, fq12zero)  (* Point at infinity - shouldn't happen in miller loop *)
  else let
    m = f12div (f12sub y2 y1) (f12sub x2 x1);
    x3 = f12sub (f12sub (f12sqr m) x1) x2;
    y3 = f12sub (mulFQ12 m (f12sub x1 x3)) y1
  in (x3, y3)
End

val () = cv_trans f12_add_def;

(* Line function: evaluate line through P1, P2 at point T *)
(* linefunc(P1, P2, T) = m * (xt - x1) - (yt - y1) where m is slope *)
Definition f12_linefunc_def:
  f12_linefunc (x1, y1) (x2, y2) (xt, yt) =
  if x1 = x2 then
    if y1 = y2 then
      (* Tangent line: m = 3*x1^2 / (2*y1) *)
      let m = f12div (mulFQ12 (embed_fq 3n) (f12sqr x1))
                     (f12add y1 y1)
      in f12sub (mulFQ12 m (f12sub xt x1)) (f12sub yt y1)
    else
      (* Vertical line *)
      f12sub xt x1
  else
    (* Chord line: m = (y2 - y1) / (x2 - x1) *)
    let m = f12div (f12sub y2 y1) (f12sub x2 x1)
    in f12sub (mulFQ12 m (f12sub xt x1)) (f12sub yt y1)
End

val () = cv_trans f12_linefunc_def;

Definition f2frobenius_def:
  f2frobenius (c0, c1) = (c0, fneg c1)
End

val () = cv_trans f2frobenius_def;

(* Frobenius p^1 coefficients for Fq6 and Fq12 *)
Definition frob1_c1_def:
  frob1_c1 =
    (8376118865763821496583973867626364092589906065868298776909617916018768340080n,
     16469823323077808223889137241176536799009286646108169935659301613961712198316n)
End

val () = cv_trans_deep_embedding EVAL frob1_c1_def;

Definition frob1_c2_def:
  frob1_c2 = (21888242871839275220042445260109153167277707414472061641714758635765020556616n, 0n)
End

val () = cv_trans_deep_embedding EVAL frob1_c2_def;

(* Frobenius p^2 coefficients *)
Definition frob2_c1_def:
  frob2_c1 = (21888242871839275220042445260109153167277707414472061641714758635765020556617n, 0n)
End

val () = cv_trans_deep_embedding EVAL frob2_c1_def;

Definition frob2_c2_def:
  frob2_c2 = (21888242871839275220042445260109153167277707414472061641714758635765020556616n, 0n)
End

val () = cv_trans_deep_embedding EVAL frob2_c2_def;

(* Twist Frobenius coefficients for optimal ate pairing *)
(* These are used for Q1 and Q2 in the miller loop final additions *)
(* twist_frob1_x = xi^((p-1)/3) for Q1 x-coordinate *)
Definition twist_frob1_x_def:
  twist_frob1_x =
    (21575463638280843010398324269430826099269044274347216827212613867836435027261n,
     10307601595873709700152284273816112264069230130616436755625194854815875713954n)
End

val () = cv_trans_deep_embedding EVAL twist_frob1_x_def;

(* twist_frob1_y = xi^((p-1)/2) for Q1 y-coordinate *)
Definition twist_frob1_y_def:
  twist_frob1_y =
    (2821565182194536844548159561693502659359617185244120367078079554186484126554n,
     3505843767911556378687030309984248845540243509899259641013678093033130930403n)
End

val () = cv_trans_deep_embedding EVAL twist_frob1_y_def;

(* Frobenius p^3 coefficients *)
Definition frob3_c1_def:
  frob3_c1 =
    (2581911344467009335267311115468803099551665605076196740867805258568234346338n,
     19937756971775647987995932169929341994314640652964949448313374472400716661030n)
End

val () = cv_trans_deep_embedding EVAL frob3_c1_def;

Definition frob3_c2_def:
  frob3_c2 = (2203960485148121921418603742825762020974279258880205651966n, 0n)
End

val () = cv_trans_deep_embedding EVAL frob3_c2_def;

Definition f6frobenius_p1_def:
  f6frobenius_p1 (c0, (c1, c2)) =
    (f2frobenius c0,
     (f2mul (f2frobenius c1) frob1_c1,
      f2mul (f2frobenius c2) frob1_c2))
End

val () = cv_trans f6frobenius_p1_def;

Definition f6frobenius_p2_def:
  f6frobenius_p2 (c0, (c1, c2)) =
    (f2frobenius c0,
     (f2mul (f2frobenius c1) frob2_c1,
      f2mul (f2frobenius c2) frob2_c2))
End

val () = cv_trans f6frobenius_p2_def;

Definition f6frobenius_p3_def:
  f6frobenius_p3 (c0, (c1, c2)) =
    (f2frobenius c0,
     (f2mul (f2frobenius c1) frob3_c1,
      f2mul (f2frobenius c2) frob3_c2))
End

val () = cv_trans f6frobenius_p3_def;

Definition f12frobenius_p1_def:
  f12frobenius_p1 (c0, c1) =
    (f6frobenius_p1 c0,
     f6mul (f6frobenius_p1 c1) (frob1_c1, ((0n,0n), (0n,0n))))
End

val () = cv_trans f12frobenius_p1_def;

Definition f12frobenius_p2_def:
  f12frobenius_p2 (c0, c1) =
    (f6frobenius_p2 c0,
     f6mul (f6frobenius_p2 c1) (frob2_c1, ((0n,0n), (0n,0n))))
End

val () = cv_trans f12frobenius_p2_def;

Definition f12frobenius_p3_def:
  f12frobenius_p3 (c0, c1) =
    (f6frobenius_p3 c0,
     f6mul (f6frobenius_p3 c1) (frob3_c1, ((0n,0n), (0n,0n))))
End

val () = cv_trans f12frobenius_p3_def;

(* Poly12 Frobenius coefficients: w^i maps to frob_a_i * w^i + frob_b_i * w^((i+6) mod 12) *)
(* These are the precomputed values of (w^q)^i mod (w^12 - 18*w^6 + 82) *)
(* From py_ecc: w^i -> (coeff at w^i) * w^i + (coeff at w^((i+6) mod 12)) * w^((i+6) mod 12) *)
Definition frob1_a_def:
  frob1_a (i:num) =
    if i = 0n then 1n else
    if i = 1n then 13365409060938474037306578913838458522380504351979534994799168652879942015317n else
    if i = 2n then 16360020762774556598013388786114916077431217727990580677342011753074458436007n else
    if i = 3n then 15045457014669079880857698262349813226890047910746430923333052506178758170093n else
    if i = 4n then 20136284445039654443521573293420200948986700144072064670248776058768820274315n else
    if i = 5n then 12213237718317714435432069045728674390396718360292308943147966475590979932072n else
    if i = 6n then 21888242871839275222246405745257275088696311157297823662689037894645226208582n else
    if i = 7n then 8522833810900801184939826831418816566315806805318288667889869241765284193266n else
    if i = 8n then 5528222109064718624233016959142359011265093429307242985347026141570767772576n else
    if i = 9n then 6842785857170195341388707482907461861806263246551392739355985388466468038490n else
    if i = 10n then 1751958426799620778724832451837074139709611013225758992440261835876405934268n else
    if i = 11n then 9675005153521560786814336699528600698299592797005514719541071419054246276511n else 0n
End

Definition frob1_b_def:
  frob1_b (i:num) =
    if i = 0n then 0n else
    if i = 1n then 16469823323077808223889137241176536799009286646108169935659301613961712198316n else
    if i = 2n then 10307601595873709700152284273816112264069230130616436755625194854815875713954n else
    if i = 3n then 3505843767911556378687030309984248845540243509899259641013678093033130930403n else
    if i = 4n then 19937756971775647987995932169929341994314640652964949448313374472400716661030n else
    if i = 5n then 8447204650696766136447902020341177575205426561248465145919723016860428151883n else
    if i = 6n then 18n else
    if i = 7n then 15149388816844991028686460567044464535476179991058260916837039682243069519642n else
    if i = 8n then 1515075255943902619915209849611390435230609634891435693592219128690297546038n else
    if i = 9n then 11091343436809180351614910509573166200913051272729455615890601373803728140145n else
    if i = 10n then 5519090358942869774631834397357627544196820822321065521472227381981946161077n else
    if i = 11n then 15091102541443398914402572935544421557437151058424932771830130262738472679799n else 0n
End

val () = cv_trans frob1_a_def;
val () = cv_trans frob1_b_def;

(* Frobenius p^1: f(w) -> f(w^q) using precomputed constants *)
(* Each c_i * w^i becomes c_i * (frob1_a(i) * w^i + frob1_b(i) * w^((i+6) mod 12)) *)
(* So r_j = c_j * frob1_a(j) + c_{(j+6) mod 12} * frob1_b((j+6) mod 12) *)
Definition poly12_frobenius_p1_def:
  poly12_frobenius_p1 (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11) = let
    r0 = fadd (fmul c0 (frob1_a 0n)) (fmul c6 (frob1_b 6n));
    r1 = fadd (fmul c1 (frob1_a 1n)) (fmul c7 (frob1_b 7n));
    r2 = fadd (fmul c2 (frob1_a 2n)) (fmul c8 (frob1_b 8n));
    r3 = fadd (fmul c3 (frob1_a 3n)) (fmul c9 (frob1_b 9n));
    r4 = fadd (fmul c4 (frob1_a 4n)) (fmul c10 (frob1_b 10n));
    r5 = fadd (fmul c5 (frob1_a 5n)) (fmul c11 (frob1_b 11n));
    r6 = fadd (fmul c6 (frob1_a 6n)) (fmul c0 (frob1_b 0n));
    r7 = fadd (fmul c7 (frob1_a 7n)) (fmul c1 (frob1_b 1n));
    r8 = fadd (fmul c8 (frob1_a 8n)) (fmul c2 (frob1_b 2n));
    r9 = fadd (fmul c9 (frob1_a 9n)) (fmul c3 (frob1_b 3n));
    r10 = fadd (fmul c10 (frob1_a 10n)) (fmul c4 (frob1_b 4n));
    r11 = fadd (fmul c11 (frob1_a 11n)) (fmul c5 (frob1_b 5n))
  in (r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11)
End

val () = cv_trans poly12_frobenius_p1_def;

(* Frobenius p^2: apply Frobenius twice *)
Definition poly12_frobenius_p2_def:
  poly12_frobenius_p2 p = poly12_frobenius_p1 (poly12_frobenius_p1 p)
End

val () = cv_trans poly12_frobenius_p2_def;

(* Frobenius p^3: apply Frobenius three times *)
Definition poly12_frobenius_p3_def:
  poly12_frobenius_p3 p = poly12_frobenius_p1 (poly12_frobenius_p2 p)
End

val () = cv_trans poly12_frobenius_p3_def;

(* Poly12 conjugation: negate odd coefficients (for FQ12, conjugation is raising to p^6) *)
(* In poly basis, p^6 negates w^(odd) terms since w^6 has order 2 in the quotient *)
Definition poly12_f12conj_def:
  poly12_f12conj (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11) =
    (c0, fneg c1, c2, fneg c3, c4, fneg c5, c6, fneg c7, c8, fneg c9, c10, fneg c11)
End

val () = cv_trans poly12_f12conj_def;

(* Miller loop for optimal Ate pairing on bn254 *)
(* The loop parameter is 6x + 2 where x = 4965661367192848881 *)
(* This equals 29793968203157093288 *)
(* We iterate using NAF (non-adjacent form) for efficiency *)
(* The NAF of 6x+2 has the following non-zero positions: *)
(* Bits set to 1: positions 0,1,3,4,5,7,9,10,12,17,20,23,29,34,37,42,45,49,51,53,56,58,61,63 *)
(* Bits set to -1: positions 62 *)

Definition ate_loop_count_def:
  ate_loop_count = 29793968203157093288n
End

val () = cv_trans_deep_embedding EVAL ate_loop_count_def;

(* Miller loop iteration - py_ecc style working entirely in FQ12 *)
Definition miller_loop_iter_def:
  miller_loop_iter r q f p n =
  if n = 0 then (r, f)
  else let
    (* Double step: f = f^2 * line(R, R, P); R = 2R *)
    line_dbl = f12_linefunc r r p;
    f' = mulFQ12 (f12sqr f) line_dbl;
    r' = f12_double r;
    (* Add step if bit is set *)
    (r'', f'') = if ODD n then
      let line_add = f12_linefunc r' q p;
          f'' = mulFQ12 f' line_add;
          r'' = f12_add r' q
      in (r'', f'')
    else (r', f');
    n' = n DIV 2
  in miller_loop_iter r'' q f'' p n'
Termination
  WF_REL_TAC `measure (λ(_,_,_,_,n). n)`
End

val () = cv_trans miller_loop_iter_def;

(* Complete Miller loop for bn254 - py_ecc style *)
(* Everything works in FQ12 after twisting Q *)
Definition miller_loop_def:
  miller_loop qx qy (px, py) =
  if (qx = f2zero ∧ qy = f2zero) ∨ (px = 0 ∧ py = 0) then fq12one
  else let
    (* Twist Q into FQ12 *)
    q = (twist_x qx, twist_y qy);
    (* Embed P into FQ12 *)
    p = (embed_fq px, embed_fq py);
    (* Main loop *)
    rf = miller_loop_iter q q fq12one p ate_loop_count;
    r = FST rf;
    f = SND rf;
    (* Frobenius corrections: Q1 = pi(Q), -Q2 = -pi^2(Q) *)
    (* In FQ12: pi(x, y) = (x^p, y^p) *)
    q1 = (f12frobenius_p1 (FST q), f12frobenius_p1 (SND q));
    (* -Q2: apply Frobenius again and negate y *)
    q2x = f12frobenius_p1 (FST q1);
    q2y = f12sub fq12zero (f12frobenius_p1 (SND q1));
    nq2 = (q2x, q2y);
    (* Final line evaluations *)
    f' = mulFQ12 f (f12_linefunc r q1 p);
    r' = f12_add r q1;
    f'' = mulFQ12 f' (f12_linefunc r' nq2 p)
  in f''
End

val () = cv_trans miller_loop_def;

(* Final exponentiation for bn254 pairing *)
(* Raises f to the power (p^12 - 1) / n *)
(* Split into: easy part (p^6 - 1)(p^2 + 1) and hard part (p^4 - p^2 + 1)/n *)

(* Easy part of final exponentiation *)
Definition final_exp_easy_def:
  final_exp_easy f = let
    (* f^(p^6 - 1) = conj(f) * inv(f) *)
    t0 = f12conj f;
    t1 = f12inv f;
    t2 = mulFQ12 t0 t1;
    (* f^((p^6-1)(p^2+1)) = t2^(p^2) * t2 *)
    t3 = f12frobenius_p2 t2
  in mulFQ12 t3 t2
End

val () = cv_trans final_exp_easy_def;

(* Exponentiation by x = 4965661367192848881 using square-and-multiply *)
Definition f12_exp_x_loop_def:
  f12_exp_x_loop f acc n =
  if n = 0 then acc
  else let
    acc' = if ODD n then mulFQ12 acc f else acc;
    f' = f12sqr f;
    n' = n DIV 2
  in f12_exp_x_loop f' acc' n'
Termination
  WF_REL_TAC `measure (λ(_,_,n). n)`
End

val () = cv_trans f12_exp_x_loop_def;

Definition bn254_x_def:
  bn254_x = 4965661367192848881n
End

val () = cv_trans_deep_embedding EVAL bn254_x_def;

Definition f12_exp_x_def:
  f12_exp_x f = f12_exp_x_loop f fq12one bn254_x
End

val () = cv_trans f12_exp_x_def;

(* Hard part of final exponentiation using the BN-specific formula *)
(* Uses the fact that for BN curves, we can compute this efficiently *)
Definition final_exp_hard_def:
  final_exp_hard f = let
    (* Various powers of f needed *)
    y0 = f12sqr f;
    y1 = f12_exp_x y0;
    y2 = f12_exp_x (f12sqr y1);
    y3 = f12conj f;
    y1 = mulFQ12 y1 y3;
    y1 = f12conj y1;
    y1 = mulFQ12 y1 y2;
    y2 = f12_exp_x y1;
    y3 = f12_exp_x y2;
    y1 = f12conj y1;
    y3 = mulFQ12 y1 y3;
    y1 = f12conj y1;
    y1 = f12frobenius_p3 y1;
    y2 = f12frobenius_p2 y2;
    y1 = mulFQ12 y1 y2;
    y2 = f12_exp_x y3;
    y2 = mulFQ12 y2 y0;
    y2 = mulFQ12 y2 f;
    y1 = mulFQ12 y1 y2;
    y2 = f12frobenius_p1 y3;
    y1 = mulFQ12 y1 y2
  in y1
End

val () = cv_trans final_exp_hard_def;

(* Complete final exponentiation *)
Definition final_exponentiation_def:
  final_exponentiation f = final_exp_hard (final_exp_easy f)
End

val () = cv_trans final_exponentiation_def;

(* Complete optimal Ate pairing on bn254 *)
Definition pairing_def:
  pairing qx qy p = final_exponentiation (miller_loop qx qy p)
End

val () = cv_trans pairing_def;

(* ======== Poly12-based pairing (matching py_ecc) ======== *)

(* Poly12 miller loop iteration - MSB-first version *)
(* Processes bits from position i down to 0 *)
(* ate_loop_count has 65 bits, we start at position 63 (log_ate_loop_count) *)
(* i is num, uses i+1 iterations, terminates when i = 0 after processing bit 0 *)
(* Uses ODD(n DIV 2**i) instead of BIT i n for cv_trans compatibility *)
Definition poly12_miller_iter_def:
  poly12_miller_iter r q f p n (i:num) =
  let
    line_dbl = poly12_linefunc r r p;
    f' = poly12_mul (poly12_sqr f) line_dbl;
    r' = poly12_double r;
    (r'', f'') = if ODD (n DIV (2 ** i)) then
      let line_add = poly12_linefunc r' q p;
          f'' = poly12_mul f' line_add;
          r'' = poly12_point_add r' q
      in (r'', f'')
    else (r', f')
  in if i = 0 then (r'', f'')
     else poly12_miller_iter r'' q f'' p n (i - 1)
Termination
  WF_REL_TAC `measure (λ(_,_,_,_,_,i). i)`
End

val () = cv_trans poly12_miller_iter_def;

(* log_ate_loop_count = 63 (floor of log2(ate_loop_count)) *)
Definition log_ate_loop_count_def:
  log_ate_loop_count = 63n
End

val () = cv_trans log_ate_loop_count_def;

(* Complete poly12 miller loop *)
Definition poly12_miller_loop_def:
  poly12_miller_loop qx qy (px, py) =
  if (qx = f2zero ∧ qy = f2zero) ∨ (px = 0 ∧ py = 0) then poly12_one
  else let
    q = (poly12_twist_x qx, poly12_twist_y qy);
    p = (poly12_embed_fq px, poly12_embed_fq py);
    rf = poly12_miller_iter q q poly12_one p ate_loop_count log_ate_loop_count;
    r = FST rf;
    f = SND rf;
    q1 = (poly12_frobenius_p1 (FST q), poly12_frobenius_p1 (SND q));
    q2x = poly12_frobenius_p1 (FST q1);
    q2y = poly12_sub poly12_zero (poly12_frobenius_p1 (SND q1));
    nq2 = (q2x, q2y);
    f' = poly12_mul f (poly12_linefunc r q1 p);
    r' = poly12_point_add r q1;
    f'' = poly12_mul f' (poly12_linefunc r' nq2 p)
  in f''
End

val () = cv_trans poly12_miller_loop_def;

(* Poly12 final exponentiation - easy part *)
Definition poly12_final_exp_easy_def:
  poly12_final_exp_easy f = let
    t0 = poly12_f12conj f;
    t1 = poly12_inv f;
    t2 = poly12_mul t0 t1;
    t3 = poly12_frobenius_p2 t2
  in poly12_mul t3 t2
End

val () = cv_trans poly12_final_exp_easy_def;

(* Poly12 exponentiation by x *)
Definition poly12_exp_x_loop_def:
  poly12_exp_x_loop f acc n =
  if n = 0 then acc
  else let
    acc' = if ODD n then poly12_mul acc f else acc;
    f' = poly12_sqr f;
    n' = n DIV 2
  in poly12_exp_x_loop f' acc' n'
Termination
  WF_REL_TAC `measure (λ(_,_,n). n)`
End

val () = cv_trans poly12_exp_x_loop_def;

Definition poly12_exp_x_def:
  poly12_exp_x f = poly12_exp_x_loop f poly12_one bn254_x
End

val () = cv_trans poly12_exp_x_def;

(* Poly12 final exponentiation - hard part *)
Definition poly12_final_exp_hard_def:
  poly12_final_exp_hard f = let
    y0 = poly12_sqr f;
    y1 = poly12_exp_x y0;
    y2 = poly12_exp_x (poly12_sqr y1);
    y3 = poly12_f12conj f;
    y1 = poly12_mul y1 y3;
    y1 = poly12_f12conj y1;
    y1 = poly12_mul y1 y2;
    y2 = poly12_exp_x y1;
    y3 = poly12_exp_x y2;
    y1 = poly12_f12conj y1;
    y3 = poly12_mul y1 y3;
    y1 = poly12_f12conj y1;
    y1 = poly12_frobenius_p3 y1;
    y2 = poly12_frobenius_p2 y2;
    y1 = poly12_mul y1 y2;
    y2 = poly12_exp_x y3;
    y2 = poly12_mul y2 y0;
    y2 = poly12_mul y2 f;
    y1 = poly12_mul y1 y2;
    y2 = poly12_frobenius_p1 y3;
    y1 = poly12_mul y1 y2
  in y1
End

val () = cv_trans poly12_final_exp_hard_def;

(* Final exponentiation exponent: (p^12 - 1) / r *)
Definition final_exp_exp_def:
  final_exp_exp = 552484233613224096312617126783173147097382103762957654188882734314196910839907541213974502761540629817009608548654680343627701153829446747810907373256841551006201639677726139946029199968412598804882391702273019083653272047566316584365559776493027495458238373902875937659943504873220554161550525926302303331747463515644711876653177129578303191095900909191624817826566688241804408081892785725967931714097716709526092261278071952560171111444072049229123565057483750161460024353346284167282452756217662335528813519139808291170539072125381230815729071544861602750936964829313608137325426383735122175229541155376346436093930287402089517426973178917569713384748081827255472576937471496195752727188261435633271238710131736096299798168852925540549342330775279877006784354801422249722573783561685179618816480037695005515426162362431072245638324744480n
End

val () = cv_trans final_exp_exp_def;

(* Complete poly12 final exponentiation - simple approach like py_ecc *)
Definition poly12_final_exp_def:
  poly12_final_exp f = poly12_exp_x_loop f poly12_one final_exp_exp
End

val () = cv_trans poly12_final_exp_def;

(* Complete poly12 pairing *)
Definition poly12_pairing_def:
  poly12_pairing qx qy p = poly12_final_exp (poly12_miller_loop qx qy p)
End

val () = cv_trans poly12_pairing_def;
