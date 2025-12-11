Theory bn254 (* aka alt_bn128 *)
Ancestors
  vfmTypes
  arithmetic
  list
  rich_list
Libs
  cv_transLib
  wordsLib

(* ============================================================ *)
(* Base field Fq: integers mod bn254p                           *)
(* ============================================================ *)

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

Definition fneg_def:
  fneg x = if x = 0 then 0 else bn254p - x
End

val () = cv_trans fneg_def;

(* Extended Euclidean algorithm for modular inverse *)
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
  WF_REL_TAC `measure FST`
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

(* ============================================================ *)
(* G1: Elliptic curve over Fq (projective coordinates)          *)
(* ============================================================ *)

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

(* ============================================================ *)
(* Fq2: Quadratic extension Fq[i] / (i^2 + 1)                   *)
(* Elements are pairs (a, b) representing a + b*i               *)
(* ============================================================ *)

Definition f2zero_def:
  f2zero = (0n, 0n)
End

val () = cv_trans_deep_embedding EVAL f2zero_def;

Definition f2one_def:
  f2one = (1n, 0n)
End

val () = cv_trans_deep_embedding EVAL f2one_def;

Definition f2add_def:
  f2add (x1,xi) (y1,yi) =
    (fadd x1 y1, fadd xi yi)
End

val () = cv_trans f2add_def;

Definition f2sub_def:
  f2sub (x1,xi) (y1,yi) =
    (fsub x1 y1, fsub xi yi)
End

val () = cv_trans f2sub_def;

Definition f2neg_def:
  f2neg (x1,xi) =
    (fneg x1, fneg xi)
End

val () = cv_trans f2neg_def;

(* Multiplication using Karatsuba:
   (a + bi)(c + di) = (ac - bd) + (ad + bc)i
                    = (ac - bd) + ((a+b)(c+d) - ac - bd)i *)
Definition f2mul_def:
  f2mul (x1,xi) (y1,yi) = let
    t1 = fmul x1 y1;
    t2 = fmul xi yi;
    o1 = fsub t1 t2;
    oi = fsub (fmul (fadd x1 xi) (fadd y1 yi)) (fadd t1 t2)
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
    c = fadd x1 x1
  in (fmul a b, fmul c xi)
End

val () = cv_trans f2sqr_def;

Definition f2inv_def:
  f2inv (x1, xi) = let
    fr = finv (fadd (fmul x1 x1) (fmul xi xi))
  in (fmul fr x1, fmul fr (fneg xi))
End

val () = cv_trans f2inv_def;

Definition f2div_def:
  f2div x y =
  f2mul x (f2inv y)
End

val () = cv_trans f2div_def;

(* ============================================================ *)
(* G2: Elliptic curve over Fq2                                  *)
(* ============================================================ *)

Definition bn254bF2_def:
  bn254bF2 =
  (19485874751759354771024239261021720505790618469301721065564631296452457478373n,
   266929791119991161246907387137283842545076965332900288569378510910307636690n)
End

val () = cv_trans_deep_embedding EVAL bn254bF2_def;

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
    rx = f2mul (f2mul (f2mul (f2sub t0 t3) x) y) f2div2;
    ry = f2sub (f2sqr (f2mul (f2add t0 t3) f2div2)) (f2muls (f2sqr t2) 3);
    rz = f2mul t0 t4
  in (rx, (ry, rz))
End

val () = cv_trans dbl6_def;

Definition add6_def:
  add6 (rx, (ry, rz)) (qx,qy) = let
    t0 = f2sub ry (f2mul qy rz);
    t1 = f2sub rx (f2mul qx rz);
    t2 = f2sqr t1;
    t3 = f2mul t2 t1;
    t4 = f2mul t2 rx;
    t5 = f2add (f2sub t3 (f2muls t4 2))
               (f2mul (f2sqr t0) rz);
    rx = f2mul t1 t5;
    ry = f2sub (f2mul (f2sub t4 t5) t0)
               (f2mul t3 ry);
    rz = f2mul rz t3
  in (rx, (ry, rz))
End

val () = cv_trans add6_def;

Definition mulF2_loop_def:
  mulF2_loop a p n =
  if n = 0 then a
  else let
    a = if ODD n then add6 a (FST p, FST (SND p)) else a;
    p = dbl6 p;
    n = n DIV 2
  in mulF2_loop a p n
End

val () = cv_trans mulF2_loop_def;

Definition zeroF2_def:
  zeroF2 = (f2zero, (f2one, f2zero))
End

val () = cv_trans_deep_embedding EVAL zeroF2_def;

Definition mulF2_def:
  mulF2 p n =
  if n = 0 then zeroF2
  else mulF2_loop zeroF2 p (n MOD bn254n)
End

val () = cv_trans mulF2_def;

Definition toAffineF2_def:
  toAffineF2 (x, (y, z)) =
  if z = f2one then (x, y)
  else if z = f2zero then (f2zero, f2zero)
  else let iz = f2inv z in (f2mul x iz, f2mul y iz)
End

val () = cv_trans toAffineF2_def;

Definition fromAffineF2_def:
  fromAffineF2 (x, y) =
  if (x, y) = (f2zero, f2zero) then zeroF2 else (x, (y, f2one))
End

val () = cv_trans fromAffineF2_def;

Definition mulAffineF2_def:
  mulAffineF2 p n = toAffineF2 (mulF2 (fromAffineF2 p) n)
End

val () = cv_trans mulAffineF2_def;

Definition weierstrassEquationF2_def:
  weierstrassEquationF2 x = let
    x2 = f2mul x x;
    x3 = f2mul x2 x
  in f2add x3 bn254bF2
End

val () = cv_trans weierstrassEquationF2_def;

Definition validAffineF2_def:
  validAffineF2 (x, y) =
  (FST x < bn254p ∧ SND x < bn254p ∧
   FST y < bn254p ∧ SND y < bn254p ∧
   ((x, y) = (f2zero, f2zero) ∨
    f2mul y y = weierstrassEquationF2 x))
End

val () = cv_trans validAffineF2_def;

(* ============================================================ *)
(* FQ12: Polynomial representation as 12-tuples                 *)
(* Polynomial ring Fq[w] / (w^12 - 18*w^6 + 82)                 *)
(* Tuple (c0,...,c11) represents c0 + c1*w + ... + c11*w^11     *)
(* ============================================================ *)

Definition poly12_zero_def:
  poly12_zero = (0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n)
End

val () = cv_trans_deep_embedding EVAL poly12_zero_def;

Definition poly12_one_def:
  poly12_one = (1n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n)
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

Definition poly12_scale_def:
  poly12_scale s (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11) =
    (fmul s a0, fmul s a1, fmul s a2, fmul s a3,
     fmul s a4, fmul s a5, fmul s a6, fmul s a7,
     fmul s a8, fmul s a9, fmul s a10, fmul s a11)
End

val () = cv_trans poly12_scale_def;

(* Reduce degree-12+ polynomial using w^12 = 18*w^6 - 82 *)
Definition poly12_reduce_def:
  poly12_reduce (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,
                 c13,c14,c15,c16,c17,c18,c19,c20,c21,c22) = let
    (* c22*w^22 = c22*w^10*(18*w^6 - 82) = 18*c22*w^16 - 82*c22*w^10 *)
    c16 = fadd c16 (fmul 18n c22); c10 = fsub c10 (fmul 82n c22);
    c15 = fadd c15 (fmul 18n c21); c9 = fsub c9 (fmul 82n c21);
    c14 = fadd c14 (fmul 18n c20); c8 = fsub c8 (fmul 82n c20);
    c13 = fadd c13 (fmul 18n c19); c7 = fsub c7 (fmul 82n c19);
    c12 = fadd c12 (fmul 18n c18); c6 = fsub c6 (fmul 82n c18);
    c11 = fadd c11 (fmul 18n c17); c5 = fsub c5 (fmul 82n c17);
    c10 = fadd c10 (fmul 18n c16); c4 = fsub c4 (fmul 82n c16);
    c9 = fadd c9 (fmul 18n c15); c3 = fsub c3 (fmul 82n c15);
    c8 = fadd c8 (fmul 18n c14); c2 = fsub c2 (fmul 82n c14);
    c7 = fadd c7 (fmul 18n c13); c1 = fsub c1 (fmul 82n c13);
    c6 = fadd c6 (fmul 18n c12); c0 = fsub c0 (fmul 82n c12)
  in (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11)
End

val () = cv_trans poly12_reduce_def;

(* Polynomial multiplication with reduction *)
Definition poly12_mul_def:
  poly12_mul (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11)
             (b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11) = let
    c0 = fmul a0 b0;
    c1 = fadd (fmul a0 b1) (fmul a1 b0);
    c2 = fadd (fadd (fmul a0 b2) (fmul a1 b1)) (fmul a2 b0);
    c3 = fadd (fadd (fadd (fmul a0 b3) (fmul a1 b2)) (fmul a2 b1)) (fmul a3 b0);
    c4 = fadd (fadd (fadd (fadd (fmul a0 b4) (fmul a1 b3)) (fmul a2 b2)) (fmul a3 b1)) (fmul a4 b0);
    c5 = fadd (fadd (fadd (fadd (fadd (fmul a0 b5) (fmul a1 b4)) (fmul a2 b3)) (fmul a3 b2)) (fmul a4 b1)) (fmul a5 b0);
    c6 = fadd (fadd (fadd (fadd (fadd (fadd (fmul a0 b6) (fmul a1 b5)) (fmul a2 b4)) (fmul a3 b3)) (fmul a4 b2)) (fmul a5 b1)) (fmul a6 b0);
    c7 = fadd (fadd (fadd (fadd (fadd (fadd (fadd (fmul a0 b7) (fmul a1 b6)) (fmul a2 b5)) (fmul a3 b4)) (fmul a4 b3)) (fmul a5 b2)) (fmul a6 b1)) (fmul a7 b0);
    c8 = fadd (fadd (fadd (fadd (fadd (fadd (fadd (fadd (fmul a0 b8) (fmul a1 b7)) (fmul a2 b6)) (fmul a3 b5)) (fmul a4 b4)) (fmul a5 b3)) (fmul a6 b2)) (fmul a7 b1)) (fmul a8 b0);
    c9 = fadd (fadd (fadd (fadd (fadd (fadd (fadd (fadd (fadd (fmul a0 b9) (fmul a1 b8)) (fmul a2 b7)) (fmul a3 b6)) (fmul a4 b5)) (fmul a5 b4)) (fmul a6 b3)) (fmul a7 b2)) (fmul a8 b1)) (fmul a9 b0);
    c10 = fadd (fadd (fadd (fadd (fadd (fadd (fadd (fadd (fadd (fadd (fmul a0 b10) (fmul a1 b9)) (fmul a2 b8)) (fmul a3 b7)) (fmul a4 b6)) (fmul a5 b5)) (fmul a6 b4)) (fmul a7 b3)) (fmul a8 b2)) (fmul a9 b1)) (fmul a10 b0);
    c11 = fadd (fadd (fadd (fadd (fadd (fadd (fadd (fadd (fadd (fadd (fadd (fmul a0 b11) (fmul a1 b10)) (fmul a2 b9)) (fmul a3 b8)) (fmul a4 b7)) (fmul a5 b6)) (fmul a6 b5)) (fmul a7 b4)) (fmul a8 b3)) (fmul a9 b2)) (fmul a10 b1)) (fmul a11 b0);
    c12 = fadd (fadd (fadd (fadd (fadd (fadd (fadd (fadd (fadd (fadd (fmul a1 b11) (fmul a2 b10)) (fmul a3 b9)) (fmul a4 b8)) (fmul a5 b7)) (fmul a6 b6)) (fmul a7 b5)) (fmul a8 b4)) (fmul a9 b3)) (fmul a10 b2)) (fmul a11 b1);
    c13 = fadd (fadd (fadd (fadd (fadd (fadd (fadd (fadd (fadd (fmul a2 b11) (fmul a3 b10)) (fmul a4 b9)) (fmul a5 b8)) (fmul a6 b7)) (fmul a7 b6)) (fmul a8 b5)) (fmul a9 b4)) (fmul a10 b3)) (fmul a11 b2);
    c14 = fadd (fadd (fadd (fadd (fadd (fadd (fadd (fadd (fmul a3 b11) (fmul a4 b10)) (fmul a5 b9)) (fmul a6 b8)) (fmul a7 b7)) (fmul a8 b6)) (fmul a9 b5)) (fmul a10 b4)) (fmul a11 b3);
    c15 = fadd (fadd (fadd (fadd (fadd (fadd (fadd (fmul a4 b11) (fmul a5 b10)) (fmul a6 b9)) (fmul a7 b8)) (fmul a8 b7)) (fmul a9 b6)) (fmul a10 b5)) (fmul a11 b4);
    c16 = fadd (fadd (fadd (fadd (fadd (fadd (fmul a5 b11) (fmul a6 b10)) (fmul a7 b9)) (fmul a8 b8)) (fmul a9 b7)) (fmul a10 b6)) (fmul a11 b5);
    c17 = fadd (fadd (fadd (fadd (fadd (fmul a6 b11) (fmul a7 b10)) (fmul a8 b9)) (fmul a9 b8)) (fmul a10 b7)) (fmul a11 b6);
    c18 = fadd (fadd (fadd (fadd (fmul a7 b11) (fmul a8 b10)) (fmul a9 b9)) (fmul a10 b8)) (fmul a11 b7);
    c19 = fadd (fadd (fadd (fmul a8 b11) (fmul a9 b10)) (fmul a10 b9)) (fmul a11 b8);
    c20 = fadd (fadd (fmul a9 b11) (fmul a10 b10)) (fmul a11 b9);
    c21 = fadd (fmul a10 b11) (fmul a11 b10);
    c22 = fmul a11 b11
  in poly12_reduce (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,
                    c13,c14,c15,c16,c17,c18,c19,c20,c21,c22)
End

val () = cv_trans poly12_mul_def;

Definition poly12_sqr_def:
  poly12_sqr x = poly12_mul x x
End

val () = cv_trans poly12_sqr_def;

(* ============================================================ *)
(* List-based polynomial operations for FQ12 inverse            *)
(* Polynomials represented as coefficient lists, highest first  *)
(* e.g., [a; b; c] represents a*x^2 + b*x + c                   *)
(* ============================================================ *)

(* Strip leading zeros from polynomial *)
Definition poly_normalize_def:
  poly_normalize [] = [] /\
  poly_normalize (x::xs) = if x = 0n then poly_normalize xs else x::xs
End

val () = cv_trans poly_normalize_def;

(* Negate a polynomial (0 - each coeff) *)
Definition poly_neg_def:
  poly_neg [] = [] /\
  poly_neg (x::xs) = fsub 0n x :: poly_neg xs
End

val () = cv_trans poly_neg_def;

(* Helper: pairwise subtraction of equal-length lists *)
Definition poly_sub_aligned_def:
  poly_sub_aligned [] [] = [] /\
  poly_sub_aligned (x::xs) (y::ys) = fsub x y :: poly_sub_aligned xs ys /\
  poly_sub_aligned _ _ = []
End

val () = cv_trans poly_sub_aligned_def;

(* Polynomial subtraction - aligns by degree (pads shorter at head) *)
Definition poly_sub_def:
  poly_sub xs ys =
    let lx = LENGTH xs;
        ly = LENGTH ys;
        xs' = if lx < ly then REPLICATE (ly - lx) 0n ++ xs else xs;
        ys' = if ly < lx then REPLICATE (lx - ly) 0n ++ ys else ys
    in poly_sub_aligned xs' ys'
End

val () = cv_trans poly_sub_def;

(* Helper: pairwise addition of equal-length lists *)
Definition poly_add_aligned_def:
  poly_add_aligned [] [] = [] /\
  poly_add_aligned (x::xs) (y::ys) = fadd x y :: poly_add_aligned xs ys /\
  poly_add_aligned _ _ = []
End

val () = cv_trans poly_add_aligned_def;

(* Polynomial addition - aligns by degree (pads shorter at head) *)
Definition poly_add_def:
  poly_add xs ys =
    let lx = LENGTH xs;
        ly = LENGTH ys;
        xs' = if lx < ly then REPLICATE (ly - lx) 0n ++ xs else xs;
        ys' = if ly < lx then REPLICATE (lx - ly) 0n ++ ys else ys
    in poly_add_aligned xs' ys'
End

val () = cv_trans poly_add_def;

(* Scale polynomial by a scalar *)
Definition poly_scale_def:
  poly_scale s [] = [] /\
  poly_scale s (x::xs) = fmul s x :: poly_scale s xs
End

val () = cv_trans poly_scale_def;

(* Length lemmas for termination *)
Theorem poly_normalize_length_le:
  !xs. LENGTH (poly_normalize xs) <= LENGTH xs
Proof
  Induct \\ rw [poly_normalize_def]
QED

Theorem poly_sub_aligned_length:
  !xs ys. LENGTH xs = LENGTH ys ==> LENGTH (poly_sub_aligned xs ys) = LENGTH xs
Proof
  Induct \\ Cases_on `ys` \\ rw [poly_sub_aligned_def]
QED

Theorem poly_sub_length_eq:
  !xs ys. LENGTH xs = LENGTH ys ==> LENGTH (poly_sub xs ys) = LENGTH xs
Proof
  rw [poly_sub_def, poly_sub_aligned_length]
QED

Theorem poly_scale_length:
  !s xs. LENGTH (poly_scale s xs) = LENGTH xs
Proof
  Induct_on `xs` \\ rw [poly_scale_def]
QED

(* Tail-recursive polynomial divmod helper *)
Definition poly_divmod_aux_def:
  poly_divmod_aux xs ys acc =
    case xs of
    | [] => ([], acc)
    | (x::xs') =>
        case ys of
        | [] => ([], x::xs')
        | (y::ys') =>
            if LENGTH xs' < LENGTH ys'
            then (x::xs', acc)
            else let
              c = fdiv x y;
              zeroes = REPLICATE (LENGTH xs' - LENGTH ys') 0n;
              cys = poly_scale c (ys' ++ zeroes);
              xs'' = poly_normalize (poly_sub xs' cys)
            in poly_divmod_aux xs'' ys (acc ++ [c])
Termination
  WF_REL_TAC `measure (λ(xs,ys,acc). LENGTH xs)`
  \\ rpt strip_tac
  \\ irule LESS_EQ_LESS_TRANS
  \\ irule_at Any poly_normalize_length_le
  \\ simp [poly_sub_length_eq, poly_scale_length, LENGTH_APPEND, LENGTH_REPLICATE]
End

val () = cv_trans poly_divmod_aux_def;

(* Polynomial divmod: returns (remainder, quotient) *)
Definition poly_divmod_def:
  poly_divmod xs ys = poly_divmod_aux xs ys []
End

val () = cv_trans poly_divmod_def;

(* Polynomial remainder *)
Definition poly_mod_def:
  poly_mod xs ys = FST (poly_divmod xs ys)
End

val () = cv_trans poly_mod_def;

(* Polynomial quotient *)
Definition poly_div_def:
  poly_div xs ys = SND (poly_divmod xs ys)
End

val () = cv_trans poly_div_def;

(* Simple polynomial multiplication *)
Definition poly_mul_simple_def:
  poly_mul_simple [] _ = [] /\
  poly_mul_simple _ [] = [] /\
  poly_mul_simple (x::xs) ys =
    poly_add (poly_scale x ys ++ REPLICATE (LENGTH xs) 0n)
             (poly_mul_simple xs ys)
End

val () = cv_trans poly_mul_simple_def;

(* Key lemma: poly_normalize reduces length when head is zero *)
Theorem poly_normalize_length:
  !xs. LENGTH (poly_normalize xs) <= LENGTH xs
Proof
  Induct \\ rw [poly_normalize_def]
QED

Theorem poly_neg_length:
  !xs. LENGTH (poly_neg xs) = LENGTH xs
Proof
  Induct \\ rw [poly_neg_def]
QED

Theorem poly_sub_length:
  !xs ys. LENGTH (poly_sub xs ys) = MAX (LENGTH xs) (LENGTH ys)
Proof
  rw [poly_sub_def, poly_sub_aligned_length, MAX_DEF, LENGTH_APPEND, LENGTH_REPLICATE]
QED

Theorem poly_divmod_aux_length:
  ∀xs ys acc. ys ≠ [] ⇒ LENGTH (FST (poly_divmod_aux xs ys acc)) < LENGTH ys
Proof
  ho_match_mp_tac poly_divmod_aux_ind \\ rw []
  \\ once_rewrite_tac [poly_divmod_aux_def]
  \\ Cases_on `xs` \\ Cases_on `ys` \\ simp []
  \\ gvs [] \\ gvs []
  \\ IF_CASES_TAC \\ simp []
QED

(* Key lemma for termination: remainder is strictly shorter than divisor *)
Theorem poly_mod_length:
  !xs ys. ys <> [] ==> LENGTH (poly_mod xs ys) < LENGTH ys
Proof
  rw [poly_mod_def, poly_divmod_def, poly_divmod_aux_length]
QED

(* ============================================================ *)
(* Fixed-size FQ12 inverse following py_ecc exactly            *)
(* Uses 13-tuples for fixed size, ascending order (c0 first)  *)
(* ============================================================ *)

(* Type: poly13 = 13-tuple representing degree <= 12 polynomial in ascending order *)
(* (c0, c1, c2, ..., c12) represents c0 + c1*w + c2*w^2 + ... + c12*w^12 *)

(* Get coefficient at index i from poly13 - using EL on list conversion for cv_trans compatibility *)
Definition poly13_to_list_def:
  poly13_to_list (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12) =
    [c0;c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12]
End

val () = cv_trans poly13_to_list_def;

Definition list_to_poly13_def:
  list_to_poly13 xs =
    (if LENGTH xs > 0 then EL 0 xs else 0n,
     if LENGTH xs > 1 then EL 1 xs else 0n,
     if LENGTH xs > 2 then EL 2 xs else 0n,
     if LENGTH xs > 3 then EL 3 xs else 0n,
     if LENGTH xs > 4 then EL 4 xs else 0n,
     if LENGTH xs > 5 then EL 5 xs else 0n,
     if LENGTH xs > 6 then EL 6 xs else 0n,
     if LENGTH xs > 7 then EL 7 xs else 0n,
     if LENGTH xs > 8 then EL 8 xs else 0n,
     if LENGTH xs > 9 then EL 9 xs else 0n,
     if LENGTH xs > 10 then EL 10 xs else 0n,
     if LENGTH xs > 11 then EL 11 xs else 0n,
     if LENGTH xs > 12 then EL 12 xs else 0n)
End

val list_to_poly13_pre_def = cv_trans_pre "list_to_poly13_pre" list_to_poly13_def;

Theorem list_to_poly13_pre[cv_pre]:
  ∀xs. list_to_poly13_pre xs
Proof
  rw [list_to_poly13_pre_def]
  \\ Cases_on `xs` \\ gvs []
QED

Definition poly13_get_def:
  poly13_get p i = EL i (poly13_to_list p)
End

val poly13_get_pre_def = cv_trans_pre "poly13_get_pre" poly13_get_def;

Theorem poly13_get_pre[cv_pre]:
  ∀p i. i < 13 ⇒ poly13_get_pre p i
Proof
  rw [poly13_get_pre_def]
  \\ PairCases_on `p` \\ gvs [poly13_to_list_def]
QED

(* Set coefficient at index i in poly13 *)
Definition poly13_set_def:
  poly13_set p i v = list_to_poly13 (LUPDATE v i (poly13_to_list p))
End

val () = cv_trans poly13_set_def;

(* Zero poly13 *)
Definition poly13_zero_def:
  poly13_zero = (0n,0n,0n,0n,0n,0n,0n,0n,0n,0n,0n,0n,0n)
End

val () = cv_trans_deep_embedding EVAL poly13_zero_def;

Theorem poly13_get_zero:
  ∀j. j ≤ 12 ⇒ poly13_get poly13_zero j = 0
Proof
  simp[LESS_OR_EQ, wordsTheory.NUMERAL_LESS_THM]
  \\ rw[] \\ EVAL_TAC
QED

(* Compute degree of poly13 (highest index with non-zero coeff) *)
Definition poly13_deg_def:
  poly13_deg (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12) =
    if c12 <> 0n then 12n else
    if c11 <> 0n then 11n else
    if c10 <> 0n then 10n else
    if c9 <> 0n then 9n else
    if c8 <> 0n then 8n else
    if c7 <> 0n then 7n else
    if c6 <> 0n then 6n else
    if c5 <> 0n then 5n else
    if c4 <> 0n then 4n else
    if c3 <> 0n then 3n else
    if c2 <> 0n then 2n else
    if c1 <> 0n then 1n else
    0n
End

val () = cv_trans poly13_deg_def;

Theorem poly13_deg_le_12:
  ∀p. poly13_deg p ≤ 12
Proof
  PairCases \\ rw [poly13_deg_def]
QED

(* Inner loop j for truncated multiply-subtract:
   out[i+j] -= a[i] * b[j] for j from 0 to 12-i *)
Definition poly13_mulsub_inner_def:
  poly13_mulsub_inner out a_i b i j =
    if j > 12 - i then out
    else let
      idx = i + j;
      b_j = poly13_get b j;
      cur = poly13_get out idx;
      new_val = fsub cur (fmul a_i b_j);
      out' = poly13_set out idx new_val
    in poly13_mulsub_inner out' a_i b i (j + 1)
Termination
  WF_REL_TAC `measure (\(out,a_i,b,i,j). 13 - j)`
End

val poly13_mulsub_inner_pre_def = cv_trans_pre "poly13_mulsub_inner_pre" poly13_mulsub_inner_def;

Theorem poly13_to_list_length:
  ∀p. LENGTH (poly13_to_list p) = 13
Proof
  PairCases \\ rw [poly13_to_list_def]
QED

Theorem poly13_mulsub_inner_pre[cv_pre]:
  ∀out a_i b i j. i ≤ 12 ⇒ poly13_mulsub_inner_pre out a_i b i j
Proof
  ho_match_mp_tac poly13_mulsub_inner_ind
  \\ rw []
  \\ rw [Once poly13_mulsub_inner_pre_def]
  \\ rw [poly13_get_pre_def, poly13_to_list_length]
QED

(* Outer loop i for truncated multiply-subtract:
   for i in 0..12: for j in 0..(12-i): out[i+j] -= a[i] * b[j] *)
Definition poly13_mulsub_outer_def:
  poly13_mulsub_outer out a b i =
    if i > 12 then out
    else let
      a_i = poly13_get a i;
      out' = poly13_mulsub_inner out a_i b i 0
    in poly13_mulsub_outer out' a b (i + 1)
Termination
  WF_REL_TAC `measure (\(out,a,b,i). 13 - i)`
End

val poly13_mulsub_outer_pre_def = cv_trans_pre "poly13_mulsub_outer_pre" poly13_mulsub_outer_def;

Theorem poly13_mulsub_outer_pre[cv_pre]:
  ∀out a b i. poly13_mulsub_outer_pre out a b i
Proof
  ho_match_mp_tac poly13_mulsub_outer_ind
  \\ rw []
  \\ rw [Once poly13_mulsub_outer_pre_def]
  \\ rw [poly13_get_pre_def, poly13_to_list_length, poly13_mulsub_inner_pre]
QED

(* Truncated multiply-subtract: out - a * b (truncated to degree 12) *)
Definition poly13_mulsub_def:
  poly13_mulsub out a b = poly13_mulsub_outer out a b 0
End

val () = cv_trans poly13_mulsub_def;

(* Inner loop for poly_rounded_div: temp[c+i] -= o[c] for c from 0 to degb *)
Definition poly13_div_sub_inner_def:
  poly13_div_sub_inner temp o_acc degb i c =
    if c > degb then temp
    else let
      idx = c + i;
      cur = poly13_get temp idx;
      o_c = poly13_get o_acc c;
      new_val = fsub cur o_c;
      temp' = poly13_set temp idx new_val
    in poly13_div_sub_inner temp' o_acc degb i (c + 1)
Termination
  WF_REL_TAC `measure (\(temp,o_acc,degb,i,c). degb + 1 - c)`
End

val poly13_div_sub_inner_pre_def = cv_trans_pre "poly13_div_sub_inner_pre" poly13_div_sub_inner_def;

Theorem poly13_div_sub_inner_pre[cv_pre]:
  ∀temp o_acc degb i c. degb ≤ 12 ∧ i + degb ≤ 12 ⇒ poly13_div_sub_inner_pre temp o_acc degb i c
Proof
  ho_match_mp_tac poly13_div_sub_inner_ind
  \\ rw []
  \\ rw [Once poly13_div_sub_inner_pre_def]
  \\ rw [poly13_get_pre_def, poly13_to_list_length]
QED

(* poly_rounded_div matching py_ecc exactly (ascending order)
   py_ecc iterates i from dega-degb down to 0, so we do the same *)
Definition poly13_rounded_div_outer_def:
  poly13_rounded_div_outer temp o_acc b degb dega i =
    if i > dega - degb then o_acc
    else let
      (* Compute index from high to low: actual_i = dega - degb - i *)
      actual_i = dega - degb - i;
      (* o[actual_i] += temp[degb + actual_i] / b[degb] *)
      temp_idx = degb + actual_i;
      cur_o = poly13_get o_acc actual_i;
      new_o = fadd cur_o (fdiv (poly13_get temp temp_idx) (poly13_get b degb));
      o_acc' = poly13_set o_acc actual_i new_o;
      (* for c in 0..degb: temp[c+actual_i] -= o[c] *)
      temp' = poly13_div_sub_inner temp o_acc' degb actual_i 0
    in poly13_rounded_div_outer temp' o_acc' b degb dega (i + 1)
Termination
  WF_REL_TAC `measure (\(temp,o_acc,b,degb,dega,i). (dega - degb + 1) - i)`
End

val poly13_rounded_div_outer_pre_def = cv_trans_pre "poly13_rounded_div_outer_pre" poly13_rounded_div_outer_def;

Theorem poly13_rounded_div_outer_pre[cv_pre]:
  ∀temp o_acc b degb dega i. dega ≤ 12 ∧ degb ≤ 12 ⇒ poly13_rounded_div_outer_pre temp o_acc b degb dega i
Proof
  ho_match_mp_tac poly13_rounded_div_outer_ind
  \\ rw []
  \\ rw [Once poly13_rounded_div_outer_pre_def]
  \\ rw [poly13_get_pre_def, poly13_to_list_length, poly13_div_sub_inner_pre]
QED

(* py_ecc's poly_rounded_div: returns quotient of a/b *)
Definition poly13_rounded_div_def:
  poly13_rounded_div a b =
    let dega = poly13_deg a;
        degb = poly13_deg b
    in if degb > dega then poly13_zero
       else poly13_rounded_div_outer a poly13_zero b degb dega 0
End

val poly13_rounded_div_pre_def = cv_trans_pre "poly13_rounded_div_pre" poly13_rounded_div_def;

Theorem poly13_rounded_div_pre[cv_pre]:
  ∀a b. poly13_rounded_div_pre a b
Proof
  rw [poly13_rounded_div_pre_def, poly13_rounded_div_outer_pre, poly13_deg_le_12]
QED

(* FQ12 modulus in ascending order: 82 - 18*w^6 + w^12 *)
Definition poly13_modulus_def:
  poly13_modulus = (82n, 0n, 0n, 0n, 0n, 0n,
    21888242871839275222246405745257275088696311157297823662689037894645226208565n,
    0n, 0n, 0n, 0n, 0n, 1n)
End

val () = cv_trans_deep_embedding EVAL poly13_modulus_def;

(* Convert poly12 (descending, 12-tuple) to poly13 (ascending, 13-tuple) *)
Definition poly12_to_poly13_def:
  poly12_to_poly13 (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11) =
    (c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, 0n)
End

val () = cv_trans poly12_to_poly13_def;

(* Convert poly13 (ascending) to poly12 (descending) *)
Definition poly13_to_poly12_def:
  poly13_to_poly12 (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12) =
    (c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11)
End

val () = cv_trans poly13_to_poly12_def;

(* ============================================================ *)
(* Fresh 13-tuple EEA implementation following py_ecc exactly   *)
(* All operations in ascending order, fuel-based termination    *)
(* ============================================================ *)

(* poly13 one: [1, 0, 0, ..., 0] *)
Definition poly13_one_def:
  poly13_one = (1n,0n,0n,0n,0n,0n,0n,0n,0n,0n,0n,0n,0n)
End

val () = cv_trans_deep_embedding EVAL poly13_one_def;

(* Pad quotient r to 13 elements (py_ecc does: r += [0] * (degree + 1 - len(r))) *)
(* Since we use fixed 13-tuples, this is already done *)

(* EEA loop with fuel - follows py_ecc inv() exactly:
   while deg(low):
     r = poly_rounded_div(high, low)
     nm = hm - lm * r  (truncated)
     new = high - low * r (truncated)
     lm, low, hm, high = nm, new, lm, low
   return lm[:degree] / low[0]
*)
Definition poly13_inv_loop_def:
  poly13_inv_loop fuel lm hm low high =
    if fuel = 0n then (lm, poly13_get low 0)
    else if poly13_deg low = 0 then (lm, poly13_get low 0)
    else
      let
        r = poly13_rounded_div high low;
        nm = poly13_mulsub hm lm r;
        new = poly13_mulsub high low r
      in poly13_inv_loop (fuel - 1) nm lm new low
End

val poly13_inv_loop_pre_def = cv_trans_pre "poly13_inv_loop_pre" poly13_inv_loop_def;

(* Prove the precondition for poly13_inv_loop *)
Theorem poly13_inv_loop_pre[cv_pre]:
  ∀fuel lm hm low high. poly13_inv_loop_pre fuel lm hm low high
Proof
  ho_match_mp_tac poly13_inv_loop_ind
  \\ rw []
  \\ simp [Once poly13_inv_loop_pre_def]
  \\ rw [poly13_get_pre_def]
  \\ PairCases_on `low` \\ gvs [poly13_to_list_def]
QED

(* Scale poly13 by a field element *)
Definition poly13_scale_def:
  poly13_scale s (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12) =
    (fmul s c0, fmul s c1, fmul s c2, fmul s c3,
     fmul s c4, fmul s c5, fmul s c6, fmul s c7,
     fmul s c8, fmul s c9, fmul s c10, fmul s c11, fmul s c12)
End

val () = cv_trans poly13_scale_def;

(* Complete poly13 inverse following py_ecc *)
Definition poly13_inv_def:
  poly13_inv coeffs =
    let
      lm = poly13_one;
      hm = poly13_zero;
      low = coeffs;
      high = poly13_modulus;
      (* 30 iterations is more than enough for degree 12 *)
      (result_lm, c) = poly13_inv_loop 30 lm hm low high;
      inv_c = finv c
    in poly13_scale inv_c result_lm
End

val () = cv_trans poly13_inv_def;

(* poly12_inv using poly13 operations *)
Definition poly12_inv_via_poly13_def:
  poly12_inv_via_poly13 p =
    poly13_to_poly12 (poly13_inv (poly12_to_poly13 p))
End

val () = cv_trans poly12_inv_via_poly13_def;

(* poly12_inv uses the fresh poly13-based implementation *)
Definition poly12_inv_def:
  poly12_inv p = poly12_inv_via_poly13 p
End

val () = cv_trans poly12_inv_def;

(* Polynomial division in FQ12 *)
Definition poly12_div_def:
  poly12_div x y = poly12_mul x (poly12_inv y)
End

val () = cv_trans poly12_div_def;

(* ============================================================ *)
(* Twist functions: embed G2 points (over Fq2) into FQ12        *)
(* ============================================================ *)

(* Twist isomorphism: (a, b) -> (a - 9*b, b) *)
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

(* Embed Fq element at position 0 *)
Definition poly12_embed_fq_def:
  poly12_embed_fq x = (x, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n)
End

val () = cv_trans poly12_embed_fq_def;

(* ============================================================ *)
(* Poly12 point operations (affine coordinates)                 *)
(* ============================================================ *)

Definition poly12_double_def:
  poly12_double (x1, y1) = let
    m = poly12_div (poly12_mul (poly12_embed_fq 3n) (poly12_sqr x1))
                   (poly12_add y1 y1);
    x3 = poly12_sub (poly12_sqr m) (poly12_add x1 x1);
    y3 = poly12_sub (poly12_mul m (poly12_sub x1 x3)) y1
  in (x3, y3)
End

val () = cv_trans poly12_double_def;

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

(* ============================================================ *)
(* Frobenius endomorphism                                       *)
(* ============================================================ *)

(* Precomputed Frobenius coefficients for w^i -> frob1_a(i)*w^i + frob1_b(i)*w^((i+6) mod 12) *)
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

(* Frobenius p^1: f(w) -> f(w^q) *)
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

Definition poly12_frobenius_p2_def:
  poly12_frobenius_p2 p = poly12_frobenius_p1 (poly12_frobenius_p1 p)
End

val () = cv_trans poly12_frobenius_p2_def;

Definition poly12_frobenius_p3_def:
  poly12_frobenius_p3 p = poly12_frobenius_p1 (poly12_frobenius_p2 p)
End

val () = cv_trans poly12_frobenius_p3_def;

(* Conjugation: negate odd coefficients (= raising to p^6) *)
Definition poly12_conj_def:
  poly12_conj (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11) =
    (c0, fneg c1, c2, fneg c3, c4, fneg c5, c6, fneg c7, c8, fneg c9, c10, fneg c11)
End

val () = cv_trans poly12_conj_def;

(* ============================================================ *)
(* Miller loop (MSB-first, following py_ecc)                    *)
(* ============================================================ *)

Definition ate_loop_count_def:
  ate_loop_count = 29793968203157093288n
End

val () = cv_trans_deep_embedding EVAL ate_loop_count_def;

Definition log_ate_loop_count_def:
  log_ate_loop_count = 63n
End

val () = cv_trans log_ate_loop_count_def;

(* Miller loop iteration - MSB-first *)
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

(* Complete Miller loop *)
Definition miller_loop_def:
  miller_loop qx qy (px, py) =
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

val () = cv_trans miller_loop_def;

(* ============================================================ *)
(* Final exponentiation                                         *)
(* ============================================================ *)

(* Exponent: (p^12 - 1) / r *)
Definition final_exp_exp_def:
  final_exp_exp = 552484233613224096312617126783173147097382103762957654188882734314196910839907541213974502761540629817009608548654680343627701153829446747810907373256841551006201639677726139946029199968412598804882391702273019083653272047566316584365559776493027495458238373902875937659943504873220554161550525926302303331747463515644711876653177129578303191095900909191624817826566688241804408081892785725967931714097716709526092261278071952560171111444072049229123565057483750161460024353346284167282452756217662335528813519139808291170539072125381230815729071544861602750936964829313608137325426383735122175229541155376346436093930287402089517426973178917569713384748081827255472576937471496195752727188261435633271238710131736096299798168852925540549342330775279877006784354801422249722573783561685179618816480037695005515426162362431072245638324744480n
End

val () = cv_trans final_exp_exp_def;

(* Simple exponentiation loop *)
Definition poly12_exp_loop_def:
  poly12_exp_loop f acc n =
  if n = 0 then acc
  else let
    acc' = if ODD n then poly12_mul acc f else acc;
    f' = poly12_sqr f;
    n' = n DIV 2
  in poly12_exp_loop f' acc' n'
Termination
  WF_REL_TAC `measure (λ(_,_,n). n)`
End

val () = cv_trans poly12_exp_loop_def;

(* Final exponentiation: f^((p^12-1)/r) *)
Definition final_exponentiation_def:
  final_exponentiation f = poly12_exp_loop f poly12_one final_exp_exp
End

val () = cv_trans final_exponentiation_def;

(* ============================================================ *)
(* Complete pairing                                             *)
(* ============================================================ *)

Definition pairing_def:
  pairing qx qy p = final_exponentiation (miller_loop qx qy p)
End

val () = cv_trans pairing_def;
