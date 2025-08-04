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
    oi = fsub (fmul (fadd x1 y1) (fadd xi yi)) (fadd t1 t2);
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
  dbl6 (x,y,z) = let
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
  in (rx, ry, rz)
End

val () = cv_trans dbl6_def;

Definition add6_def:
  add6 (rx,ry,rz) (qx,qy) = let
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
  in (rx, ry, rz)
End

val () = cv_trans add6_def;

Definition f2_nonresidue_def:
  f2_nonresidue = (9n, 1n)
End

val () = cv_trans_deep_embedding EVAL f2_nonresidue_def;

Definition f6mul01_def:
  f6mul01 (c0,c1,c2) b0 b1 = let
    t0 = f2mul c0 b0;
    t1 = f2mul c1 b1;
  in (
    f2add (f2mul (f2sub (f2mul (f2add c1 c2) b1) t1) f2_nonresidue) t0,
    f2sub (f2sub (f2mul (f2add b0 b1) (f2add c0 c1)) t0) t1,
    f2add (f2sub (f2mul (f2add c0 c2) b0) t0) t1
  )
End

val () = cv_trans f6mul01_def;

Definition f6add_def:
  f6add (c0,c1,c2) (r0,r1,r2) =
    (f2add c0 r0,
     f2add c1 r1,
     f2add c2 r2)
End

val () = cv_trans f6add_def;

Definition f6sub_def:
  f6sub (c0,c1,c2) (r0,r1,r2) =
    (f2sub c0 r0,
     f2sub c1 r1,
     f2sub c2 r2)
End

val () = cv_trans f6sub_def;

Definition f6mul_def:
  f6mul (c0,c1,c2) (r0,r1,r2) = let
    t0 = f2mul c0 r0;
    t1 = f2mul c1 r1;
    t2 = f2mul c2 r2;
  in (
    f2add t0 (f2mul (f2sub (f2mul (f2add c1 c2) (f2add r1 r2)) (f2add t1 t2))
              f2_nonresidue),
    f2add (f2sub (f2mul (f2add c0 c1) (f2add r0 r1)) (f2add t0 t1))
          (f2mul t2 f2_nonresidue),
    f2sub (f2add t1 (f2mul (f2add c0 c2) (f2add r0 r2)))
          (f2add t0 t2)
    )
End

val () = cv_trans f6mul_def;

Definition f6mul_nonresidue_def:
  f6mul_nonresidue (c0,c1:num#num,c2:num#num) =
    (f2mul c0 f2_nonresidue, c1, c2)
End

val () = cv_trans f6mul_nonresidue_def;

Definition f12mul034_def:
  f12mul034 (c0,c1) o0 o3 o4 = let
    a = (f2mul (FST c0) o0,
         f2mul (FST (SND c0)) o0,
         f2mul (SND (SND c0)) o0);
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

Definition mulAffineF2_def:
  mulAffineF2 (p:((num#num)#(num#num))) (n:num) = ((0n,0n),(0n,0n)) (* TODO *)
End

val () = cv_trans mulAffineF2_def;

Definition pairing_def:
  pairing (q:((num#num)#(num#num))) (p:(num#num)) =
    ((((0n,0n),(0n,0n)),
      ((0n,0n),(0n,0n)),
      ((0n,0n),(0n,0n))),
     (((0n,0n),(0n,0n)),
      ((0n,0n),(0n,0n)),
      ((0n,0n),(0n,0n)))) (* TODO *)
End

val () = cv_trans pairing_def;

Definition mulFQ12_def:
  mulFQ12 (p:((((num#num)#(num#num))#
               ((num#num)#(num#num))#
               ((num#num)#(num#num)))#
              (((num#num)#(num#num))#
               ((num#num)#(num#num))#
               ((num#num)#(num#num)))))
          (q:((((num#num)#(num#num))#
               ((num#num)#(num#num))#
               ((num#num)#(num#num)))#
              (((num#num)#(num#num))#
               ((num#num)#(num#num))#
               ((num#num)#(num#num)))))
  =
    ((((0n,0n),(0n,0n)),
      ((0n,0n),(0n,0n)),
      ((0n,0n),(0n,0n))),
     (((0n,0n),(0n,0n)),
      ((0n,0n),(0n,0n)),
      ((0n,0n),(0n,0n)))) (* TODO *)
End

val () = cv_trans mulFQ12_def;

Definition fq12one_def:
  fq12one =
  ((((1n,0n),(0n,0n)),
    ((0n,0n),(0n,0n)),
    ((0n,0n),(0n,0n))),
   (((0n,0n),(0n,0n)),
    ((0n,0n),(0n,0n)),
    ((0n,0n),(0n,0n))))
End

val () = cv_trans_deep_embedding EVAL fq12one_def;

val () = export_theory();
