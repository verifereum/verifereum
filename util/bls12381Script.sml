Theory bls12381 (* BLS12-381 curve for KZG commitments *)
Ancestors
  vfmTypes
  arithmetic
  list
  rich_list
Libs
  cv_transLib
  wordsLib

(* ============================================================ *)
(* Base field Fq: integers mod bls12381p                        *)
(* ============================================================ *)

(* Field modulus for BLS12-381 *)
Definition bls12381p_def:
  bls12381p = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787n
End

val () = cv_trans_deep_embedding EVAL bls12381p_def;

(* Curve order (subgroup order) *)
Definition bls12381n_def:
  bls12381n = 52435875175126190479447740508185965837690552500527637822603658699938581184513n
End

val () = cv_trans_deep_embedding EVAL bls12381n_def;

(* Curve parameter b: y^2 = x^3 + 4 *)
Definition bls12381b_def:
  bls12381b = 4n
End

val () = cv_trans_deep_embedding EVAL bls12381b_def;

(* ============================================================ *)
(* Base field arithmetic                                        *)
(* ============================================================ *)

Definition fmul_def:
  fmul x y = (x * y) MOD bls12381p
End

val () = cv_trans fmul_def;

Definition fadd_def:
  fadd x y = (x + y) MOD bls12381p
End

val () = cv_trans fadd_def;

Definition fsub_def:
  fsub x y = if x < y then x + bls12381p - y
             else (x - y) MOD bls12381p
End

val () = cv_trans fsub_def;

Definition fneg_def:
  fneg x = if x = 0 then 0 else bls12381p - x
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
  finv n = finv_loop n bls12381p 0 1 1 0
End

val () = cv_trans finv_def;

Definition fdiv_def:
  fdiv x y = fmul x (finv y)
End

val () = cv_trans fdiv_def;

(* Field exponentiation by squaring *)
Definition fexp_loop_def:
  fexp_loop b e acc =
  if e = 0n then acc
  else if ODD e then fexp_loop (fmul b b) (e DIV 2) (fmul acc b)
  else fexp_loop (fmul b b) (e DIV 2) acc
Termination
  WF_REL_TAC `measure (FST o SND)`
End

val () = cv_trans fexp_loop_def;

Definition fexp_def:
  fexp b e = fexp_loop b e 1n
End

val () = cv_trans fexp_def;

(* ============================================================ *)
(* G1: Elliptic curve over Fq (projective coordinates)          *)
(* Curve: y^2 = x^3 + 4                                         *)
(* ============================================================ *)

(* Point at infinity for G1 *)
Definition g1_zero_def:
  g1_zero = (1n, 1n, 0n)
End

val () = cv_trans_deep_embedding EVAL g1_zero_def;

(* G1 generator point *)
Definition g1_gen_def:
  g1_gen = (3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507n,
            1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569n,
            1n)
End

val () = cv_trans_deep_embedding EVAL g1_gen_def;

(* Check if G1 point is at infinity *)
Definition g1_is_inf_def:
  g1_is_inf (x:num, y:num, z:num) = (z = 0n)
End

val () = cv_trans g1_is_inf_def;

(* G1 point doubling (projective coordinates) *)
Definition g1_double_def:
  g1_double (x, y, z) =
  if z = 0 then (1n, 1n, 0n)
  else if y = 0 then (1n, 1n, 0n)
  else let
    w = fmul 3 (fmul x x);
    s = fmul y z;
    b = fmul x (fmul y s);
    h = fsub (fmul w w) (fmul 8 b);
    s_sq = fmul s s;
    x3 = fmul 2 (fmul h s);
    y3 = fsub (fmul w (fsub (fmul 4 b) h)) (fmul 8 (fmul (fmul y y) s_sq));
    z3 = fmul 8 (fmul s s_sq)
  in (x3, y3, z3)
End

val () = cv_trans g1_double_def;

(* G1 point addition (projective coordinates) *)
Definition g1_add_def:
  g1_add (x1, y1, z1) (x2, y2, z2) =
  if z1 = 0 then (x2, y2, z2)
  else if z2 = 0 then (x1, y1, z1)
  else let
    u1 = fmul y2 z1;
    u2 = fmul y1 z2;
    v1 = fmul x2 z1;
    v2 = fmul x1 z2
  in
    if v1 = v2 then
      if u1 = u2 then g1_double (x1, y1, z1)
      else (1n, 1n, 0n) (* point at infinity *)
    else let
      u = fsub u1 u2;
      v = fsub v1 v2;
      v_sq = fmul v v;
      v_sq_v2 = fmul v_sq v2;
      v_cu = fmul v v_sq;
      w = fmul z1 z2;
      a = fsub (fsub (fmul (fmul u u) w) v_cu) (fmul 2 v_sq_v2);
      x3 = fmul v a;
      y3 = fsub (fmul u (fsub v_sq_v2 a)) (fmul v_cu u2);
      z3 = fmul v_cu w
    in (x3, y3, z3)
End

val () = cv_trans g1_add_def;

(* G1 scalar multiplication using double-and-add *)
Definition g1_mul_loop_def:
  g1_mul_loop acc p n =
  if n = 0 then acc
  else let
    acc = if ODD n then g1_add acc p else acc;
    p = g1_double p;
    n = n DIV 2
  in g1_mul_loop acc p n
Termination
  WF_REL_TAC `measure (λ(acc, p, n). n)`
End

val () = cv_trans g1_mul_loop_def;

Definition g1_mul_def:
  g1_mul p n =
  if n = 0 then g1_zero
  else g1_mul_loop g1_zero p (n MOD bls12381n)
End

val () = cv_trans g1_mul_def;

(* G1 negation *)
Definition g1_neg_def:
  g1_neg (x, y, z) = (x, fneg y, z)
End

val () = cv_trans g1_neg_def;

(* Convert projective to affine *)
Definition g1_to_affine_def:
  g1_to_affine (x, y, z) =
  if z = 0 then (0n, 0n)
  else if z = 1 then (x, y)
  else let iz = finv z in (fmul x iz, fmul y iz)
End

val () = cv_trans g1_to_affine_def;

(* Convert affine to projective *)
Definition g1_from_affine_def:
  g1_from_affine (x, y) =
  if x = 0 /\ y = 0 then g1_zero
  else (x, y, 1n)
End

val () = cv_trans g1_from_affine_def;

(* ============================================================ *)
(* Fq2: Quadratic extension field                               *)
(* Fq2 = Fq[u] / (u^2 + 1), elements represented as (a, b)      *)
(* meaning a + b*u where u^2 = -1                               *)
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
  f2add (a1, b1) (a2, b2) = (fadd a1 a2, fadd b1 b2)
End

val () = cv_trans f2add_def;

Definition f2sub_def:
  f2sub (a1, b1) (a2, b2) = (fsub a1 a2, fsub b1 b2)
End

val () = cv_trans f2sub_def;

Definition f2neg_def:
  f2neg (a, b) = (fneg a, fneg b)
End

val () = cv_trans f2neg_def;

(* Fq2 multiplication: (a1 + b1*u)(a2 + b2*u) = (a1*a2 - b1*b2) + (a1*b2 + b1*a2)*u *)
(* using Karatsuba: (a1+b1)(a2+b2) - a1*a2 - b1*b2 = a1*b2 + b1*a2 *)
Definition f2mul_def:
  f2mul (a1, b1) (a2, b2) = let
    t1 = fmul a1 a2;
    t2 = fmul b1 b2;
    or = fsub t1 t2;
    oi = fsub (fmul (fadd a1 b1) (fadd a2 b2)) (fadd t1 t2)
  in (or, oi)
End

val () = cv_trans f2mul_def;

Definition f2sqr_def:
  f2sqr (a, b) = let
    t1 = fmul a a;
    t2 = fmul b b;
    or = fsub t1 t2;
    oi = fmul 2 (fmul a b)
  in (or, oi)
End

val () = cv_trans f2sqr_def;

(* Fq2 inverse using (a + bu)^-1 = (a - bu) / (a^2 + b^2) *)
Definition f2inv_def:
  f2inv (a, b) = let
    denom = fadd (fmul a a) (fmul b b);
    inv_denom = finv denom
  in (fmul a inv_denom, fneg (fmul b inv_denom))
End

val () = cv_trans f2inv_def;

Definition f2div_def:
  f2div x y = f2mul x (f2inv y)
End

val () = cv_trans f2div_def;

(* Scalar multiplication in Fq2 *)
Definition f2muls_def:
  f2muls (a, b) s = (fmul a s, fmul b s)
End

val () = cv_trans f2muls_def;

(* ============================================================ *)
(* G2: Elliptic curve over Fq2 (projective coordinates)         *)
(* Twisted curve: y^2 = x^3 + 4(1+u)                            *)
(* ============================================================ *)

(* Twisted curve parameter b2 = 4 + 4u *)
Definition g2_b_def:
  g2_b = (4n, 4n)
End

val () = cv_trans_deep_embedding EVAL g2_b_def;

(* Point at infinity for G2 *)
Definition g2_zero_def:
  g2_zero = (f2one, f2one, f2zero)
End

val () = cv_trans_deep_embedding EVAL g2_zero_def;

(* G2 generator point *)
Definition g2_gen_def:
  g2_gen = ((352701069587466618187139116011060144890029952792775240219908644239793785735715026873347600343865175952761926303160n,
             3059144344244213709971259814753781636986470325476647558659373206291635324768958432433509563104347017837885763365758n),
            (1985150602287291935568054521177171638300868978215655730859378665066344726373823718423869104263333984641494340347905n,
             927553665492332455747201965776037880757740193453592970025027978793976877002675564980949289727957565575433344219582n),
            f2one)
End

val () = cv_trans_deep_embedding EVAL g2_gen_def;

(* Check if G2 point is at infinity *)
Definition g2_is_inf_def:
  g2_is_inf (x:num#num, y:num#num, z:num#num) = (z = f2zero)
End

val () = cv_trans g2_is_inf_def;

(* G2 point doubling *)
Definition g2_double_def:
  g2_double (x, y, z) =
  if z = f2zero then g2_zero
  else if y = f2zero then g2_zero
  else let
    w = f2muls (f2sqr x) 3;
    s = f2mul y z;
    b = f2mul x (f2mul y s);
    h = f2sub (f2sqr w) (f2muls b 8);
    s_sq = f2sqr s;
    x3 = f2muls (f2mul h s) 2;
    y3 = f2sub (f2mul w (f2sub (f2muls b 4) h)) (f2muls (f2mul (f2sqr y) s_sq) 8);
    z3 = f2muls (f2mul s s_sq) 8
  in (x3, y3, z3)
End

val () = cv_trans g2_double_def;

(* G2 point addition *)
Definition g2_add_def:
  g2_add (x1, y1, z1) (x2, y2, z2) =
  if z1 = f2zero then (x2, y2, z2)
  else if z2 = f2zero then (x1, y1, z1)
  else let
    u1 = f2mul y2 z1;
    u2 = f2mul y1 z2;
    v1 = f2mul x2 z1;
    v2 = f2mul x1 z2
  in
    if v1 = v2 then
      if u1 = u2 then g2_double (x1, y1, z1)
      else g2_zero
    else let
      u = f2sub u1 u2;
      v = f2sub v1 v2;
      v_sq = f2sqr v;
      v_sq_v2 = f2mul v_sq v2;
      v_cu = f2mul v v_sq;
      w = f2mul z1 z2;
      a = f2sub (f2sub (f2mul (f2sqr u) w) v_cu) (f2muls v_sq_v2 2);
      x3 = f2mul v a;
      y3 = f2sub (f2mul u (f2sub v_sq_v2 a)) (f2mul v_cu u2);
      z3 = f2mul v_cu w
    in (x3, y3, z3)
End

val () = cv_trans g2_add_def;

(* G2 scalar multiplication *)
Definition g2_mul_loop_def:
  g2_mul_loop acc p n =
  if n = 0 then acc
  else let
    acc = if ODD n then g2_add acc p else acc;
    p = g2_double p;
    n = n DIV 2
  in g2_mul_loop acc p n
Termination
  WF_REL_TAC `measure (λ(acc, p, n). n)`
End

val () = cv_trans g2_mul_loop_def;

Definition g2_mul_def:
  g2_mul p n =
  if n = 0 then g2_zero
  else g2_mul_loop g2_zero p (n MOD bls12381n)
End

val () = cv_trans g2_mul_def;

(* G2 negation *)
Definition g2_neg_def:
  g2_neg (x, y, z) = (x, f2neg y, z)
End

val () = cv_trans g2_neg_def;

(* Convert G2 projective to affine *)
Definition g2_to_affine_def:
  g2_to_affine (x, y, z) =
  if z = f2zero then (f2zero, f2zero)
  else if z = f2one then (x, y)
  else let iz = f2inv z in (f2mul x iz, f2mul y iz)
End

val () = cv_trans g2_to_affine_def;

(* Convert G2 affine to projective *)
Definition g2_from_affine_def:
  g2_from_affine (x, y) =
  if x = f2zero /\ y = f2zero then g2_zero
  else (x, y, f2one)
End

val () = cv_trans g2_from_affine_def;

(* ============================================================ *)
(* Fq12: Extension field for pairing target group               *)
(* Represented as 12-tuple (polynomial in w, degree < 12)       *)
(* Modulus: w^12 - 2*w^6 + 2                                    *)
(* ============================================================ *)

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

Definition poly12_scale_def:
  poly12_scale s (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11) =
  (fmul s a0, fmul s a1, fmul s a2, fmul s a3,
   fmul s a4, fmul s a5, fmul s a6, fmul s a7,
   fmul s a8, fmul s a9, fmul s a10, fmul s a11)
End

val () = cv_trans poly12_scale_def;

Definition poly12_neg_def:
  poly12_neg (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11) =
  (fneg a0, fneg a1, fneg a2, fneg a3,
   fneg a4, fneg a5, fneg a6, fneg a7,
   fneg a8, fneg a9, fneg a10, fneg a11)
End

val () = cv_trans poly12_neg_def;

(* Reduce polynomial mod w^12 - 2*w^6 + 2 *)
(* The modulus means w^12 = 2*w^6 - 2 *)
(* For degree 12-17: c_i * w^i with i in [12,17], use w^12 = 2*w^6 - 2 *)
(*   c_i * w^i = c_i * w^(i-12) * w^12 = c_i * w^(i-12) * (2*w^6 - 2) *)
(*   = 2*c_i * w^(i-6) - 2*c_i * w^(i-12) *)
(* For degree 18-22: need to reduce further since result still has deg >= 12 *)
(*   w^18 = w^6 * w^12 = w^6 * (2*w^6 - 2) = 2*w^12 - 2*w^6 *)
(*        = 2*(2*w^6 - 2) - 2*w^6 = 4*w^6 - 4 - 2*w^6 = 2*w^6 - 4 *)
(*   w^19 = w * w^18 = w * (2*w^6 - 4) = 2*w^7 - 4*w *)
(*   w^20 = w^2 * w^18 = w^2 * (2*w^6 - 4) = 2*w^8 - 4*w^2 *)
(*   w^21 = w^3 * w^18 = w^3 * (2*w^6 - 4) = 2*w^9 - 4*w^3 *)
(*   w^22 = w^4 * w^18 = w^4 * (2*w^6 - 4) = 2*w^10 - 4*w^4 *)
Definition poly12_reduce_def:
  poly12_reduce (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,
                 c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22) =
  let
    (* First pass: reduce c12-c17 using w^12 = 2*w^6 - 2 *)
    (* c12*w^12 -> 2*c12*w^6 - 2*c12 *)
    r0 = fsub c0 (fmul 2 c12);
    r6 = fadd c6 (fmul 2 c12);
    r1 = fsub c1 (fmul 2 c13);
    r7 = fadd c7 (fmul 2 c13);
    r2 = fsub c2 (fmul 2 c14);
    r8 = fadd c8 (fmul 2 c14);
    r3 = fsub c3 (fmul 2 c15);
    r9 = fadd c9 (fmul 2 c15);
    r4 = fsub c4 (fmul 2 c16);
    r10 = fadd c10 (fmul 2 c16);
    r5 = fsub c5 (fmul 2 c17);
    r11 = fadd c11 (fmul 2 c17);
    (* Second pass: reduce c18-c22 using fully reduced formulas *)
    (* w^18 = 2*w^6 - 4, so c18*w^18 -> 2*c18*w^6 - 4*c18 *)
    r0 = fsub r0 (fmul 4 c18);
    r6 = fadd r6 (fmul 2 c18);
    (* w^19 = 2*w^7 - 4*w, so c19*w^19 -> 2*c19*w^7 - 4*c19*w *)
    r1 = fsub r1 (fmul 4 c19);
    r7 = fadd r7 (fmul 2 c19);
    (* w^20 = 2*w^8 - 4*w^2, so c20*w^20 -> 2*c20*w^8 - 4*c20*w^2 *)
    r2 = fsub r2 (fmul 4 c20);
    r8 = fadd r8 (fmul 2 c20);
    (* w^21 = 2*w^9 - 4*w^3, so c21*w^21 -> 2*c21*w^9 - 4*c21*w^3 *)
    r3 = fsub r3 (fmul 4 c21);
    r9 = fadd r9 (fmul 2 c21);
    (* w^22 = 2*w^10 - 4*w^4, so c22*w^22 -> 2*c22*w^10 - 4*c22*w^4 *)
    r4 = fsub r4 (fmul 4 c22);
    r10 = fadd r10 (fmul 2 c22)
  in (r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11)
End

val () = cv_trans poly12_reduce_def;

(* Multiply two degree-11 polynomials, get degree-22, then reduce *)
Definition poly12_mul_def:
  poly12_mul (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11)
             (b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11) =
  let
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
    c12 = fadd (fadd (fadd (fadd (fadd (fmul a1 b11) (fmul a2 b10)) (fmul a3 b9)) (fmul a4 b8)) (fmul a5 b7)) (fadd (fadd (fadd (fadd (fadd (fmul a6 b6) (fmul a7 b5)) (fmul a8 b4)) (fmul a9 b3)) (fmul a10 b2)) (fmul a11 b1));
    c13 = fadd (fadd (fadd (fadd (fmul a2 b11) (fmul a3 b10)) (fmul a4 b9)) (fmul a5 b8)) (fadd (fadd (fadd (fadd (fadd (fmul a6 b7) (fmul a7 b6)) (fmul a8 b5)) (fmul a9 b4)) (fmul a10 b3)) (fmul a11 b2));
    c14 = fadd (fadd (fadd (fmul a3 b11) (fmul a4 b10)) (fmul a5 b9)) (fadd (fadd (fadd (fadd (fadd (fmul a6 b8) (fmul a7 b7)) (fmul a8 b6)) (fmul a9 b5)) (fmul a10 b4)) (fmul a11 b3));
    c15 = fadd (fadd (fmul a4 b11) (fmul a5 b10)) (fadd (fadd (fadd (fadd (fadd (fmul a6 b9) (fmul a7 b8)) (fmul a8 b7)) (fmul a9 b6)) (fmul a10 b5)) (fmul a11 b4));
    c16 = fadd (fmul a5 b11) (fadd (fadd (fadd (fadd (fadd (fmul a6 b10) (fmul a7 b9)) (fmul a8 b8)) (fmul a9 b7)) (fmul a10 b6)) (fmul a11 b5));
    c17 = fadd (fadd (fadd (fadd (fadd (fmul a6 b11) (fmul a7 b10)) (fmul a8 b9)) (fmul a9 b8)) (fmul a10 b7)) (fmul a11 b6);
    c18 = fadd (fadd (fadd (fadd (fmul a7 b11) (fmul a8 b10)) (fmul a9 b9)) (fmul a10 b8)) (fmul a11 b7);
    c19 = fadd (fadd (fadd (fmul a8 b11) (fmul a9 b10)) (fmul a10 b9)) (fmul a11 b8);
    c20 = fadd (fadd (fmul a9 b11) (fmul a10 b10)) (fmul a11 b9);
    c21 = fadd (fmul a10 b11) (fmul a11 b10);
    c22 = fmul a11 b11
  in poly12_reduce (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,
                    c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22)
End

val () = cv_trans poly12_mul_def;

Definition poly12_sqr_def:
  poly12_sqr x = poly12_mul x x
End

val () = cv_trans poly12_sqr_def;

(* ============================================================ *)
(* List-based polynomial operations for FQ12 inverse            *)
(* Polynomials represented as coefficient lists, LOWEST first   *)
(* (matching py_ecc convention)                                 *)
(* e.g., [a; b; c] represents a + b*x + c*x^2                   *)
(* ============================================================ *)

(* Degree of polynomial (highest index with non-zero coeff) *)
Definition poly_deg_def:
  poly_deg [] = 0n /\
  poly_deg xs = let len = LENGTH xs in
    if LAST xs <> 0n then len - 1
    else poly_deg (FRONT xs)
Termination
  WF_REL_TAC `measure LENGTH` \\ rw [LENGTH_FRONT]
End

(* Strip trailing zeros from polynomial (lowest-first representation) *)
Definition poly_normalize_def:
  poly_normalize [] = [] /\
  poly_normalize xs = if LAST xs = 0n then poly_normalize (FRONT xs) else xs
Termination
  WF_REL_TAC `measure LENGTH` \\ rw [LENGTH_FRONT]
End

val () = cv_trans poly_deg_def;
val () = cv_trans poly_normalize_def;

(* Negate a polynomial (0 - each coeff) *)
Definition poly_neg_def:
  poly_neg [] = [] /\
  poly_neg (x::xs) = fsub 0n x :: poly_neg xs
End

val () = cv_trans poly_neg_def;

(* Helper: pairwise subtraction for same-length lists *)
Definition poly_sub_same_def:
  poly_sub_same [] [] = [] /\
  poly_sub_same (x::xs) (y::ys) = fsub x y :: poly_sub_same xs ys /\
  poly_sub_same _ _ = []  (* shouldn't happen if lists have same length *)
End

val () = cv_trans poly_sub_same_def;

(* Polynomial subtraction - for lowest-degree-first lists, pad shorter with trailing zeros *)
Definition poly_sub_def:
  poly_sub xs ys =
    let lx = LENGTH xs; ly = LENGTH ys in
    if lx < ly then
      poly_sub (xs ++ REPLICATE (ly - lx) 0n) ys
    else if ly < lx then
      poly_sub xs (ys ++ REPLICATE (lx - ly) 0n)
    else
      poly_sub_same xs ys
Termination
  WF_REL_TAC `measure (\(xs,ys). if LENGTH xs = LENGTH ys then 0 else 1)`
  \\ rw [LENGTH_APPEND, LENGTH_REPLICATE]
End

val () = cv_trans poly_sub_def;

(* Helper: pairwise addition for same-length lists *)
Definition poly_add_same_def:
  poly_add_same [] [] = [] /\
  poly_add_same (x::xs) (y::ys) = fadd x y :: poly_add_same xs ys /\
  poly_add_same _ _ = []  (* shouldn't happen if lists have same length *)
End

val () = cv_trans poly_add_same_def;

(* Polynomial addition - for lowest-degree-first lists, pad shorter with trailing zeros *)
Definition poly_add_def:
  poly_add xs ys =
    let lx = LENGTH xs; ly = LENGTH ys in
    if lx < ly then
      poly_add (xs ++ REPLICATE (ly - lx) 0n) ys
    else if ly < lx then
      poly_add xs (ys ++ REPLICATE (lx - ly) 0n)
    else
      poly_add_same xs ys
Termination
  WF_REL_TAC `measure (\(xs,ys). if LENGTH xs = LENGTH ys then 0 else 1)`
  \\ rw [LENGTH_APPEND, LENGTH_REPLICATE]
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
  ho_match_mp_tac poly_normalize_ind \\ rw []
  \\ once_rewrite_tac [poly_normalize_def]
  \\ rw [] \\ gvs [LENGTH_FRONT]
QED

Theorem poly_sub_same_length:
  !xs ys. LENGTH xs = LENGTH ys ==> LENGTH (poly_sub_same xs ys) = LENGTH xs
Proof
  Induct \\ Cases_on `ys` \\ rw [poly_sub_same_def]
QED

Theorem poly_sub_length_eq:
  !xs ys. LENGTH xs = LENGTH ys ==> LENGTH (poly_sub xs ys) = LENGTH xs
Proof
  rw [Once poly_sub_def, poly_sub_same_length]
QED

Theorem poly_scale_length:
  !s xs. LENGTH (poly_scale s xs) = LENGTH xs
Proof
  Induct_on `xs` \\ rw [poly_scale_def]
QED

(* Update list element at index (for lowest-first polynomials) *)
Definition list_update_def:
  list_update [] _ _ = [] /\
  list_update (x::xs) 0 v = v :: xs /\
  list_update (x::xs) (SUC n) v = x :: list_update xs n v
End

val () = cv_trans list_update_def;

(* Get list element at index, default 0 *)
Definition list_get_def:
  list_get [] _ = 0n /\
  list_get (x::xs) 0 = x /\
  list_get (x::xs) (SUC n) = list_get xs n
End

val () = cv_trans list_get_def;

(* Inner loop: for c in range(degb + 1): temp[c + i] -= o[c + i] * b[c] *)
Definition poly_div_inner_def:
  poly_div_inner temp o_list b i c =
    if c > poly_deg b then temp
    else let
      idx = c + i;
      temp_val = list_get temp idx;
      o_val = list_get o_list idx;
      b_val = list_get b c;
      new_val = fsub temp_val (fmul o_val b_val);
      temp' = list_update temp idx new_val
    in poly_div_inner temp' o_list b i (c + 1)
Termination
  WF_REL_TAC `measure (\(temp, o_list, b, i, c). (poly_deg b + 1) - c)`
End

val () = cv_trans poly_div_inner_def;

(* Outer loop: for i in range(dega - degb, -1, -1) - counting DOWN *)
Definition poly_div_outer_def:
  poly_div_outer temp o_list b degb i =
    if i = 0 then
      (* Last iteration with i = 0 *)
      let
        temp_at_degb_i = list_get temp degb;
        b_lead = list_get b degb;
        q = fdiv temp_at_degb_i b_lead;
        o_val = list_get o_list 0;
        o_list' = list_update o_list 0 (fadd o_val q);
        temp' = poly_div_inner temp o_list' b 0 0
      in (o_list', temp')
    else let
      (* o[i] += temp[degb + i] / b[degb] *)
      temp_at_degb_i = list_get temp (degb + i);
      b_lead = list_get b degb;
      q = fdiv temp_at_degb_i b_lead;
      o_val = list_get o_list i;
      o_list' = list_update o_list i (fadd o_val q);
      (* Inner loop *)
      temp' = poly_div_inner temp o_list' b i 0
    in poly_div_outer temp' o_list' b degb (i - 1)
Termination
  WF_REL_TAC `measure (\(temp, o_list, b, degb, i). i + 1)`
End

val () = cv_trans poly_div_outer_def;

(* Polynomial rounded division - matches py_ecc exactly *)
(* poly_rounded_div(a, b) -> quotient *)
Definition poly_rounded_div_def:
  poly_rounded_div a b = let
    dega = poly_deg a;
    degb = poly_deg b;
    temp = a;
    o_list = REPLICATE (LENGTH a) 0n;
    start_i = dega - degb;
    (result_o, result_temp) = poly_div_outer temp o_list b degb start_i
  in poly_normalize result_o
End

val () = cv_trans poly_rounded_div_def;

(* Polynomial divmod using py_ecc style division - returns (quotient, remainder) *)
Definition poly_divmod_def:
  poly_divmod a b = let
    dega = poly_deg a;
    degb = poly_deg b;
    temp = a;
    o_list = REPLICATE (LENGTH a) 0n;
    start_i = dega - degb;
    (result_o, result_temp) = poly_div_outer temp o_list b degb start_i
  in (poly_normalize result_o, poly_normalize result_temp)
End

val () = cv_trans poly_divmod_def;

(* Polynomial quotient *)
Definition poly_div_def:
  poly_div xs ys = FST (poly_divmod xs ys)
End

val () = cv_trans poly_div_def;

(* Polynomial remainder *)
Definition poly_mod_def:
  poly_mod xs ys = SND (poly_divmod xs ys)
End

val () = cv_trans poly_mod_def;

(* Simple polynomial multiplication - ascending order (constant first) *)
(* For ascending: x*ys contributes to constant, xs*ys is shifted up by 1 *)
Definition poly_mul_simple_def:
  poly_mul_simple [] _ = [] /\
  poly_mul_simple _ [] = [] /\
  poly_mul_simple (x::xs) ys =
    poly_add (poly_scale x ys)
             (0n :: poly_mul_simple xs ys)
End

val () = cv_trans poly_mul_simple_def;

Theorem poly_neg_length:
  !xs. LENGTH (poly_neg xs) = LENGTH xs
Proof
  Induct \\ rw [poly_neg_def]
QED

(* list_update preserves length *)
Theorem list_update_length:
  !xs n v. LENGTH (list_update xs n v) = LENGTH xs
Proof
  Induct \\ rw [list_update_def] \\ Cases_on `n` \\ rw [list_update_def]
QED

(* poly_deg is bounded by LENGTH *)
Theorem poly_deg_le_length:
  !xs. poly_deg xs <= LENGTH xs
Proof
  ho_match_mp_tac poly_deg_ind \\ rw [poly_deg_def]
QED

(* poly_div_inner preserves list length *)
Theorem poly_div_inner_length:
  !temp o_list b i c. LENGTH (poly_div_inner temp o_list b i c) = LENGTH temp
Proof
  ho_match_mp_tac poly_div_inner_ind \\ rw []
  \\ once_rewrite_tac [poly_div_inner_def]
  \\ IF_CASES_TAC \\ simp [list_update_length]
QED

(* poly_div_outer preserves list length in second component *)
Theorem poly_div_outer_snd_length:
  !temp o_list b degb i. LENGTH (SND (poly_div_outer temp o_list b degb i)) = LENGTH temp
Proof
  ho_match_mp_tac poly_div_outer_ind \\ rw []
  \\ once_rewrite_tac [poly_div_outer_def]
  \\ IF_CASES_TAC \\ simp [poly_div_inner_length, list_update_length]
QED

(* Descending-order normalization (strip leading zeros from head) *)
Definition poly_normalize_desc_def:
  poly_normalize_desc [] = [] /\
  poly_normalize_desc (x::xs) = if x = 0n then poly_normalize_desc xs else x::xs
End

val () = cv_trans poly_normalize_desc_def;

Theorem poly_normalize_desc_length_le:
  !xs. LENGTH (poly_normalize_desc xs) <= LENGTH xs
Proof
  Induct \\ rw [poly_normalize_desc_def]
QED

(* Descending-order poly_sub - same as ascending since element-wise *)
Definition poly_sub_desc_def:
  poly_sub_desc [] [] = [] /\
  poly_sub_desc [] ys = poly_neg ys /\
  poly_sub_desc xs [] = xs /\
  poly_sub_desc (x::xs) (y::ys) = fsub x y :: poly_sub_desc xs ys
End

val () = cv_trans poly_sub_desc_def;

Theorem poly_sub_desc_length_eq:
  !xs ys. LENGTH xs = LENGTH ys ==> LENGTH (poly_sub_desc xs ys) = LENGTH xs
Proof
  Induct \\ Cases_on `ys` \\ rw [poly_sub_desc_def]
QED

(* Tail-recursive polynomial divmod for descending order *)
(* Fixed: don't normalize during loop to preserve degree tracking *)
Definition poly_divmod_aux_desc_def:
  poly_divmod_aux_desc xs ys acc =
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
              xs'' = poly_sub_desc xs' cys
            in poly_divmod_aux_desc xs'' ys (acc ++ [c])
Termination
  WF_REL_TAC `measure (λ(xs,ys,acc). LENGTH xs)`
  \\ rw [poly_sub_desc_length_eq, poly_scale_length, LENGTH_APPEND, LENGTH_REPLICATE]
End

val () = cv_trans poly_divmod_aux_desc_def;

Definition poly_divmod_desc_def:
  poly_divmod_desc xs ys = poly_divmod_aux_desc xs ys []
End

val () = cv_trans poly_divmod_desc_def;

Definition poly_mod_desc_def:
  poly_mod_desc xs ys = FST (poly_divmod_desc xs ys)
End

val () = cv_trans poly_mod_desc_def;

Theorem poly_divmod_aux_desc_length:
  ∀xs ys acc. ys ≠ [] ⇒ LENGTH (FST (poly_divmod_aux_desc xs ys acc)) < LENGTH ys
Proof
  ho_match_mp_tac poly_divmod_aux_desc_ind \\ rw []
  \\ once_rewrite_tac [poly_divmod_aux_desc_def]
  \\ Cases_on `xs` \\ Cases_on `ys` \\ simp []
  \\ gvs [] \\ gvs []
  \\ IF_CASES_TAC \\ simp []
QED

Theorem poly_mod_desc_length:
  !xs ys. ys <> [] ==> LENGTH (poly_mod_desc xs ys) < LENGTH ys
Proof
  rw [poly_mod_desc_def, poly_divmod_desc_def, poly_divmod_aux_desc_length]
QED

(* poly_div using descending-order algorithm *)
Definition poly_div_desc_def:
  poly_div_desc xs ys = SND (poly_divmod_desc xs ys)
End

val () = cv_trans poly_div_desc_def;

(* Ascending-order normalization (strip trailing zeros) *)
Definition poly_normalize_asc_def:
  poly_normalize_asc xs = REVERSE (poly_normalize_desc (REVERSE xs))
End

val () = cv_trans poly_normalize_asc_def;

Theorem poly_normalize_asc_length_le:
  !xs. LENGTH (poly_normalize_asc xs) <= LENGTH xs
Proof
  rw [poly_normalize_asc_def]
  \\ irule LESS_EQ_TRANS
  \\ qexists_tac `LENGTH (REVERSE xs)`
  \\ simp [poly_normalize_desc_length_le]
QED

(* poly_mod using descending-order algorithm (for termination) *)
(* Normalizes inputs first, converts ascending to descending, computes, converts back *)
Definition poly_mod_via_desc_def:
  poly_mod_via_desc xs ys = let
    xs' = poly_normalize_asc xs;
    ys' = poly_normalize_asc ys
  in REVERSE (poly_mod_desc (REVERSE xs') (REVERSE ys'))
End

val () = cv_trans poly_mod_via_desc_def;

(* poly_div using descending-order algorithm *)
(* Normalizes inputs first, converts ascending to descending, computes, converts back *)
Definition poly_div_via_desc_def:
  poly_div_via_desc xs ys = let
    xs' = poly_normalize_asc xs;
    ys' = poly_normalize_asc ys
  in REVERSE (poly_div_desc (REVERSE xs') (REVERSE ys'))
End

val () = cv_trans poly_div_via_desc_def;

Theorem poly_mod_via_desc_length:
  !xs ys. poly_normalize_asc ys <> [] ==>
          LENGTH (poly_mod_via_desc xs ys) < LENGTH (poly_normalize_asc ys)
Proof
  rw [poly_mod_via_desc_def, poly_normalize_asc_def]
  \\ `poly_normalize_desc (REVERSE ys) <> []` by simp []
  \\ drule poly_mod_desc_length
  \\ simp []
QED

(* Specialized version for already-normalized inputs *)
Theorem poly_mod_via_desc_length_normalized:
  !xs ys. ys <> [] /\ poly_normalize_asc ys = ys ==>
          LENGTH (poly_mod_via_desc xs ys) < LENGTH ys
Proof
  rw []
  \\ `poly_normalize_asc ys <> []` by metis_tac []
  \\ drule poly_mod_via_desc_length \\ simp []
QED

(* poly_normalize_desc is idempotent *)
Theorem poly_normalize_desc_idempotent:
  !xs. poly_normalize_desc (poly_normalize_desc xs) = poly_normalize_desc xs
Proof
  Induct \\ rw [poly_normalize_desc_def]
QED

(* Key property: poly_mod_via_desc output is normalized (no trailing zeros) *)
(* This is because REVERSE of a normalized descending poly is normalized ascending *)
Theorem poly_normalize_desc_reverse_idempotent:
  !xs. REVERSE (poly_normalize_desc (REVERSE (REVERSE (poly_normalize_desc xs)))) =
       REVERSE (poly_normalize_desc xs)
Proof
  rw [poly_normalize_desc_idempotent]
QED

(* Extended Euclidean algorithm for polynomial inverse *)
(* Uses poly_div_via_desc and poly_mod_via_desc for consistency and easy termination *)
(* Termination: we use LENGTH (poly_normalize_asc low) as measure, which strictly decreases *)
Definition poly_inv_loop_def:
  poly_inv_loop lm hm low high =
    case poly_normalize_asc low of
    | [] => (hm, high)
    | [c] => (lm, low)
    | _ =>
        let
          r = poly_div_via_desc high low;
          nm = poly_sub hm (poly_mul_simple lm r);
          new = poly_mod_via_desc high low
        in poly_inv_loop nm lm new low
Termination
  WF_REL_TAC `measure (\(lm, hm, low, high). LENGTH (poly_normalize_asc low))`
  \\ rpt strip_tac
  \\ irule arithmeticTheory.LESS_EQ_LESS_TRANS
  \\ qexists_tac `LENGTH (poly_mod_via_desc high low)`
  \\ conj_tac
  >- (
    mp_tac (Q.SPECL [`high`, `low`] poly_mod_via_desc_length)
    \\ asm_simp_tac (srw_ss()) []
  )
  \\ simp_tac (srw_ss()) [poly_normalize_asc_length_le]
End

val poly_inv_loop_pre_def = cv_trans_pre "poly_inv_loop_pre" poly_inv_loop_def;

Theorem poly_inv_loop_pre[cv_pre]:
  ∀lm hm low high. poly_inv_loop_pre lm hm low high
Proof
  ho_match_mp_tac poly_inv_loop_ind
  \\ rw[]
  \\ rw[Once poly_inv_loop_pre_def]
  \\ gvs[]
QED

(* Conversion: 12-tuple to list (lowest degree first, like py_ecc) *)
(* Adds trailing 0 to match py_ecc's list(self.coeffs + (0,)) *)
Definition poly12_to_list_def:
  poly12_to_list (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11) =
    [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; 0n]
End

val () = cv_trans poly12_to_list_def;

(* Helper to safely get element from list *)
Definition safe_el_def:
  safe_el n [] = 0n /\
  safe_el 0 (x::xs) = x /\
  safe_el (SUC n) (x::xs) = safe_el n xs
End

val () = cv_trans safe_el_def;

(* Conversion: list to 12-tuple (lowest degree first, like py_ecc) *)
Definition list_to_poly12_def:
  list_to_poly12 xs =
    (safe_el 0 xs, safe_el 1 xs, safe_el 2 xs, safe_el 3 xs,
     safe_el 4 xs, safe_el 5 xs, safe_el 6 xs, safe_el 7 xs,
     safe_el 8 xs, safe_el 9 xs, safe_el 10 xs, safe_el 11 xs)
End

val () = cv_trans list_to_poly12_def;

(* The FQ12 modulus as a list: w^12 - 2*w^6 + 2 *)
(* Lowest degree first (like py_ecc): [2; 0; 0; 0; 0; 0; p-2; 0; 0; 0; 0; 0; 1] *)
(* py_ecc uses modulus_coeffs + (1,) which adds trailing 1 *)
Definition poly12_modulus_list_def:
  poly12_modulus_list = [2n; 0; 0; 0; 0; 0;
    4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559785n;
    0; 0; 0; 0; 0; 1]
End

val () = cv_trans_deep_embedding EVAL poly12_modulus_list_def;

(* Get leading coefficient of list polynomial *)
Definition poly_lead_def:
  poly_lead [] = 0n /\
  poly_lead (x::xs) = x
End

val () = cv_trans poly_lead_def;

(* Complete poly12 inverse using list operations - matches py_ecc exactly *)
Definition poly12_inv_def:
  poly12_inv p = let
    (* lm = [1] + [0] * degree *)
    lm = 1n :: REPLICATE 12 0n;
    (* hm = [0] * (degree + 1) *)
    hm = REPLICATE 13 0n;
    (* low = list(self.coeffs + (0,)) *)
    low = poly12_to_list p;
    (* high = list(self.modulus_coeffs + (1,)) *)
    high = poly12_modulus_list;
    (result_lm, result_low) = poly_inv_loop lm hm low high;
    (* return type(self)(lm[:degree]) / int(low[0]) *)
    inv_coeff = finv (list_get result_low 0)
  in list_to_poly12 (poly_scale inv_coeff result_lm)
End

val () = cv_trans poly12_inv_def;

(* Polynomial division in FQ12 *)
Definition poly12_div_def:
  poly12_div x y = poly12_mul x (poly12_inv y)
End

val () = cv_trans poly12_div_def;

(* ============================================================ *)
(* Twist: Embedding G2 points into Fq12                         *)
(* ============================================================ *)

(* Twist: Embedding G2 points into Fq12 *)
(* Following py_ecc exactly:
   - Field isomorphism from Z[p] / x**2 to Z[p] / x**2 - 2*x + 2
   - xcoeffs = [_x.coeffs[0] - _x.coeffs[1], _x.coeffs[1]]
   - nx = FQ12([0] + [xcoeffs[0]] + [0]*5 + [xcoeffs[1]] + [0]*4)  -- positions 1, 7
   - ny = FQ12([ycoeffs[0]] + [0]*5 + [ycoeffs[1]] + [0]*5)        -- positions 0, 6
   - nz = FQ12([0]*3 + [zcoeffs[0]] + [0]*5 + [zcoeffs[1]] + [0]*2) -- positions 3, 9
   Returns PROJECTIVE FQ12 point (nx, ny, nz)
*)
Definition twist_def:
  twist ((x0, x1), (y0, y1), (z0, z1)) =
  if (z0, z1) = f2zero then
    (poly12_zero, poly12_zero, poly12_zero)
  else let
    (* Field isomorphism: (a, b) -> (a - b, b) *)
    xcoeff0 = fsub x0 x1;
    xcoeff1 = x1;
    ycoeff0 = fsub y0 y1;
    ycoeff1 = y1;
    zcoeff0 = fsub z0 z1;
    zcoeff1 = z1;
    (* nx at positions 1 and 7 *)
    nx = (0n, xcoeff0, 0n, 0n, 0n, 0n, 0n, xcoeff1, 0n, 0n, 0n, 0n);
    (* ny at positions 0 and 6 *)
    ny = (ycoeff0, 0n, 0n, 0n, 0n, 0n, ycoeff1, 0n, 0n, 0n, 0n, 0n);
    (* nz at positions 3 and 9 *)
    nz = (0n, 0n, 0n, zcoeff0, 0n, 0n, 0n, 0n, 0n, zcoeff1, 0n, 0n)
  in (nx, ny, nz)
End

val () = cv_trans twist_def;

(* Cast G1 point to PROJECTIVE Fq12 (x, y, z) - matches py_ecc cast_point_to_fq12 *)
Definition cast_g1_to_fq12_def:
  cast_g1_to_fq12 (x, y, z) =
  ((x, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n),
   (y, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n),
   (z, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n))
End

val () = cv_trans cast_g1_to_fq12_def;

(* ============================================================ *)
(* Line function for pairing                                    *)
(* ============================================================ *)

(* PROJECTIVE line function matching py_ecc exactly.
   Returns (numerator, denominator) to avoid divisions.
   P1, P2, T are all projective FQ12 points (x, y, z).

   linefunc(P1, P2, T):
     m_numerator = y2 * z1 - y1 * z2
     m_denominator = x2 * z1 - x1 * z2
     if m_denominator != 0:  # secant
       return (m_num * (xt * z1 - x1 * zt) - m_den * (yt * z1 - y1 * zt),
               m_den * zt * z1)
     elif m_numerator == 0:  # tangent (doubling)
       m_num = 3 * x1 * x1
       m_den = 2 * y1 * z1
       return (m_num * (xt * z1 - x1 * zt) - m_den * (yt * z1 - y1 * zt),
               m_den * zt * z1)
     else:  # vertical
       return (xt * z1 - x1 * zt, z1 * zt)
*)
Definition poly12_linefunc_def:
  poly12_linefunc (x1, y1, z1) (x2, y2, z2) (xt, yt, zt) =
    let
      m_num = poly12_sub (poly12_mul y2 z1) (poly12_mul y1 z2);
      m_den = poly12_sub (poly12_mul x2 z1) (poly12_mul x1 z2)
    in
    if m_den <> poly12_zero then
      (* Secant line *)
      let
        xt_z1 = poly12_mul xt z1;
        x1_zt = poly12_mul x1 zt;
        yt_z1 = poly12_mul yt z1;
        y1_zt = poly12_mul y1 zt;
        num = poly12_sub (poly12_mul m_num (poly12_sub xt_z1 x1_zt))
                         (poly12_mul m_den (poly12_sub yt_z1 y1_zt));
        den = poly12_mul (poly12_mul m_den zt) z1
      in (num, den)
    else if m_num = poly12_zero then
      (* Tangent line (doubling) *)
      let
        m_num' = poly12_scale 3 (poly12_sqr x1);
        m_den' = poly12_scale 2 (poly12_mul y1 z1);
        xt_z1 = poly12_mul xt z1;
        x1_zt = poly12_mul x1 zt;
        yt_z1 = poly12_mul yt z1;
        y1_zt = poly12_mul y1 zt;
        num = poly12_sub (poly12_mul m_num' (poly12_sub xt_z1 x1_zt))
                         (poly12_mul m_den' (poly12_sub yt_z1 y1_zt));
        den = poly12_mul (poly12_mul m_den' zt) z1
      in (num, den)
    else
      (* Vertical line *)
      (poly12_sub (poly12_mul xt z1) (poly12_mul x1 zt),
       poly12_mul z1 zt)
End

val () = cv_trans poly12_linefunc_def;

(* ============================================================ *)
(* Miller loop for BLS12-381 Ate pairing                        *)
(* ============================================================ *)

(* Ate loop count for BLS12-381: 15132376222941642752 = 0xd201000000010000 *)
Definition ate_loop_count_def:
  ate_loop_count = 15132376222941642752n
End

val () = cv_trans_deep_embedding EVAL ate_loop_count_def;

(* Pseudo binary encoding of ate_loop_count, from py_ecc.
   This is the NAF-ish representation used for the Miller loop.
   pseudo_binary_encoding[62::-1] iterates from index 62 down to 0.
   We store it as a list from index 0 to 62 (reversed from py_ecc order). *)
Definition pseudo_binary_encoding_def:
  pseudo_binary_encoding : num list =
  [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
   1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
   0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
   1; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 1; 0; 1; 1]
End

val () = cv_trans pseudo_binary_encoding_def;

(* Miller loop iteration matching py_ecc exactly.
   R is a G2 point in Fq2 (projective), Q is the original G2 point.
   twist_Q is twist(Q).
   f_num, f_den are the accumulated numerator and denominator.
   cast_P is the G1 point cast to FQ12.
   bits is the remaining bits of pseudo_binary_encoding (reversed).

   for v in pseudo_binary_encoding[62::-1]:
     _n, _d = linefunc(twist_R, twist_R, cast_P)
     f_num = f_num * f_num * _n
     f_den = f_den * f_den * _d
     R = double(R)
     twist_R = twist(R)
     if v == 1:
       _n, _d = linefunc(twist_R, twist_Q, cast_P)
       f_num = f_num * _n
       f_den = f_den * _d
       R = add(R, Q)
       twist_R = twist(R)
*)
Definition miller_iter_def:
  miller_iter r q twist_q f_num f_den cast_p (bits:num list) =
  case bits of
  | [] => (f_num, f_den)
  | (v::rest) =>
    let
      twist_r = twist r;
      (* linefunc for doubling *)
      nd_dbl = poly12_linefunc twist_r twist_r cast_p;
      n_dbl = FST nd_dbl;
      d_dbl = SND nd_dbl;
      (* f_num = f_num^2 * n_dbl, f_den = f_den^2 * d_dbl *)
      f_num = poly12_mul (poly12_sqr f_num) n_dbl;
      f_den = poly12_mul (poly12_sqr f_den) d_dbl;
      (* R = double(R) in G2 *)
      r = g2_double r;
      (* If bit is 1, do addition step *)
      (r, f_num, f_den) =
        if v = 1 then let
          twist_r = twist r;
          nd_add = poly12_linefunc twist_r twist_q cast_p;
          n_add = FST nd_add;
          d_add = SND nd_add;
          f_num = poly12_mul f_num n_add;
          f_den = poly12_mul f_den d_add;
          r = g2_add r q
        in (r, f_num, f_den)
        else (r, f_num, f_den)
    in miller_iter r q twist_q f_num f_den cast_p rest
End

val () = cv_trans miller_iter_def;

(* Reversed pseudo binary encoding for iteration from index 62 down to 0.
   py_ecc does pseudo_binary_encoding[62::-1] which gives elements at
   indices 62, 61, 60, ..., 1, 0 (63 elements total). *)
Definition pseudo_binary_encoding_rev_def:
  pseudo_binary_encoding_rev : num list =
  [1; 0; 1; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0;
   0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
   0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0;
   0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]
End

val () = cv_trans pseudo_binary_encoding_rev_def;

(* Main Miller loop matching py_ecc *)
Definition miller_loop_def:
  miller_loop q_fq2 p =
  if g2_is_inf q_fq2 \/ g1_is_inf p then poly12_one
  else let
    cast_p = cast_g1_to_fq12 p;
    twist_q = twist q_fq2;
    result = miller_iter q_fq2 q_fq2 twist_q poly12_one poly12_one cast_p
               pseudo_binary_encoding_rev;
    f_num = FST result;
    f_den = SND result
  in poly12_div f_num f_den
End

val () = cv_trans miller_loop_def;

(* ============================================================ *)
(* Final exponentiation                                         *)
(* ============================================================ *)

(* Frobenius endomorphism: raise each coefficient to p-th power *)
(* For polynomial representation, this permutes coefficients *)
Definition poly12_frobenius_def:
  poly12_frobenius (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11) =
  (* This is a simplification - actual Frobenius involves coefficient multiplication *)
  (* For now, placeholder that would need proper Frobenius constants *)
  (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11)
End

val () = cv_trans poly12_frobenius_def;

(* Conjugation in Fq12 (for easy part of final exp) *)
Definition poly12_conj_def:
  poly12_conj (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11) =
  (a0, fneg a1, a2, fneg a3, a4, fneg a5,
   fneg a6, a7, fneg a8, a9, fneg a10, a11)
End

val () = cv_trans poly12_conj_def;

(* Final exponentiation: f^((p^12 - 1) / n) *)
(* Split into easy part: f^((p^6 - 1)(p^2 + 1)) and hard part *)
Definition final_exp_easy_def:
  final_exp_easy f = let
    (* f^(p^6-1) = f^(p^6) / f = conj(f) / f *)
    f_conj = poly12_conj f;
    f1 = poly12_div f_conj f;
    (* f^(p^2+1) = f^(p^2) * f - using Frobenius^2 *)
    f2 = poly12_mul (poly12_frobenius (poly12_frobenius f1)) f1
  in f2
End

val () = cv_trans final_exp_easy_def;

(* Exponentiation by squaring *)
Definition poly12_exp_loop_def:
  poly12_exp_loop acc base n =
  if n = 0 then acc
  else let
    acc = if ODD n then poly12_mul acc base else acc;
    base = poly12_sqr base;
    n = n DIV 2
  in poly12_exp_loop acc base n
Termination
  WF_REL_TAC `measure (λ(acc, base, n). n)`
End

val () = cv_trans poly12_exp_loop_def;

Definition poly12_exp_def:
  poly12_exp base n =
  if n = 0 then poly12_one
  else poly12_exp_loop poly12_one base n
End

val () = cv_trans poly12_exp_def;

(* Full final exponent = (p^12 - 1) / n *)
(* Following py_ecc approach: just do f^((p^12-1)/n) directly *)
Definition final_exp_def:
  final_exp =
  322277361516934140462891564586510139908379969514828494218366688025288661041104682794998680497580008899973249814104447692778988208376779573819485263026159588510513834876303014016798809919343532899164848730280942609956670917565618115867287399623286813270357901731510188149934363360381614501334086825442271920079363289954510565375378443704372994881406797882676971082200626541916413184642520269678897559532260949334760604962086348898118982248842634379637598665468817769075878555493752214492790122785850202957575200176084204422751485957336465472324810982833638490904279282696134323072515220044451592646885410572234451732790590013479358343841220074174848221722017083597872017638514103174122784843925578370430843522959600095676285723737049438346544753168912974976791528535276317256904336520179281145394686565050419250614107803233314658825463117900250701199181529205942363159325765991819433914303908860460720581408201373164047773794825411011922305820065611121544561808414055302212057471395719432072209245600258134364584636810093520285711072578721435517884103526483832733289802426157301542744476740008494780363354305116978805620671467071400711358839553375340724899735460480144599782014906586543813292157922220645089192130209334926661588737007768565838519456601560804957985667880395221049249803753582637708560n
End

val () = cv_trans_deep_embedding EVAL final_exp_def;

Definition final_exponentiation_def:
  final_exponentiation f = poly12_exp f final_exp
End

val () = cv_trans final_exponentiation_def;

(* ============================================================ *)
(* Complete pairing function                                    *)
(* ============================================================ *)

Definition pairing_def:
  pairing q p = final_exponentiation (miller_loop q p)
End

val () = cv_trans pairing_def;

(* ============================================================ *)
(* KZG Verification                                             *)
(* ============================================================ *)

(* KZG trusted setup G2 point (the "X" in X - z) *)
(* This is KZG_SETUP_G2_MONOMIAL_1 from the ceremony *)
Definition kzg_setup_g2_def:
  kzg_setup_g2 = ((3749701713850085193403383609513386037494151572263731328608276629425322978272408394373143740944003571525027436289778n,
                   3347537128081568434923729147580015899756771550835613107520576615563260658656019591232316627827007503930666726825842n),
                  (194392958648403190675529552496435226424111592982833162118538452666741235889530674000225873281133418439621742897817n,
                   3447898402727835650716129438012169492682148398295533958400255525306573911008434577489634554212211450783070687991119n),
                  f2one)
End

val () = cv_trans_deep_embedding EVAL kzg_setup_g2_def;

(* Verify KZG proof that p(z) = y *)
(* Check: e(P - y*G1, -G2) * e(proof, X - z*G2) = 1 *)
Definition verify_kzg_proof_def:
  verify_kzg_proof commitment z y proof =
  let
    (* P - y*G1 *)
    y_g1 = g1_mul g1_gen y;
    p_minus_y = g1_add commitment (g1_neg y_g1);
    (* X - z*G2 *)
    z_g2 = g2_mul g2_gen z;
    x_minus_z = g2_add kzg_setup_g2 (g2_neg z_g2);
    (* Compute pairings *)
    pairing1 = pairing (g2_neg g2_gen) p_minus_y;
    pairing2 = pairing x_minus_z proof;
    (* Product should equal 1 *)
    product = poly12_mul pairing1 pairing2
  in product = poly12_one
End

val () = cv_trans verify_kzg_proof_def;

(* ============================================================ *)
(* G1 Point Compression/Decompression                          *)
(* ============================================================ *)

(* Square root in Fq using Tonelli-Shanks *)
(* For BLS12-381, p ≡ 3 (mod 4), so sqrt(x) = x^((p+1)/4) *)
Definition fsqrt_def:
  fsqrt x = fexp x ((bls12381p + 1) DIV 4)
End

val () = cv_trans fsqrt_def;

(* Decompress a 48-byte G1 point *)
(* Returns NONE if invalid, SOME (x, y, 1) in Jacobian coords *)
Definition g1_decompress_def:
  g1_decompress (bytes: byte list) =
  if LENGTH bytes ≠ 48 then NONE else let
    (* First byte contains flags in top 3 bits *)
    first_byte = w2n (HD bytes);
    c_flag = (first_byte DIV 128) MOD 2;  (* bit 7: compression flag *)
    b_flag = (first_byte DIV 64) MOD 2;   (* bit 6: infinity flag *)
    a_flag = (first_byte DIV 32) MOD 2;   (* bit 5: y sign flag *)
    (* Extract x coordinate (mask off top 3 bits of first byte) *)
    masked_first = n2w (first_byte MOD 32) : byte;
    x_bytes = masked_first :: TL bytes;
    x = num_of_be_bytes x_bytes;
    (* Compute y² = x³ + b *)
    x3 = fmul x (fmul x x);
    y_squared = fadd x3 bls12381b;
    (* Compute y = sqrt(y²) *)
    y = fsqrt y_squared;
    (* Select correct y based on sign bit *)
    y_sign = if y > (bls12381p - 1) DIV 2 then 1 else 0;
    y_final = if y_sign = a_flag then y else fsub 0 y
  in
    (* Must be compressed format *)
    if c_flag ≠ 1 then NONE
    (* Check for point at infinity *)
    else if b_flag = 1 then
      if a_flag = 0 ∧ x = 0 then SOME g1_zero else NONE
    (* Check x is valid field element *)
    else if x >= bls12381p then NONE
    (* Verify y² = y_squared (i.e., y_squared is a quadratic residue) *)
    else if fmul y y ≠ y_squared then NONE
    else SOME (x, y_final, 1n)
End

val g1_decompress_pre_def = cv_trans_pre "g1_decompress_pre" g1_decompress_def;

Theorem g1_decompress_pre[cv_pre]:
  ∀bytes. g1_decompress_pre bytes
Proof
  rw [g1_decompress_pre_def]
  \\ Cases_on `bytes` \\ gvs []
QED
