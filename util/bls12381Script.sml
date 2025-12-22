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

(* Fq2 exponentiation by squaring *)
Definition f2exp_loop_def:
  f2exp_loop b e acc =
  if e = 0n then acc
  else if ODD e then f2exp_loop (f2mul b b) (e DIV 2) (f2mul acc b)
  else f2exp_loop (f2mul b b) (e DIV 2) acc
Termination
  WF_REL_TAC `measure (FST o SND)`
End

val () = cv_trans f2exp_loop_def;

Definition f2exp_def:
  f2exp b e = f2exp_loop b e f2one
End

val () = cv_trans f2exp_def;

(* Sign function for Fq2 (sgn0 from RFC 9380) *)
(* Returns 1 if the element is "negative" (first nonzero limb has odd value) *)
Definition f2sgn0_def:
  f2sgn0 (c0, c1) =
    let sign_0 = c0 MOD 2 in
    let zero_0 = if c0 = 0 then 1n else 0n in
    let sign_1 = c1 MOD 2 in
    sign_0 + (zero_0 * sign_1) - (sign_0 * zero_0 * sign_1)
End

val () = cv_trans f2sgn0_def;

(* Check if two Fq2 elements are equal *)
Definition f2eq_def:
  f2eq (a0, a1) (b0, b1) = ((a0 = b0) /\ (a1 = b1))
End

val () = cv_trans f2eq_def;

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
  else g2_mul_loop g2_zero p n
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

(* ============================================================ *)
(* EIP-2537 BLS12-381 Precompile Support                        *)
(* ============================================================ *)

(* Decode 64-byte field element (returns NONE if >= p) *)
Definition decode_fq_def:
  decode_fq bytes =
    if LENGTH bytes ≠ 64 then NONE
    else let n = num_of_be_bytes bytes in
         if n >= bls12381p then NONE else SOME n
End

val () = cv_trans decode_fq_def;

(* Encode field element to 64 bytes (padded) *)
Definition encode_fq_def:
  encode_fq n = PAD_LEFT 0w 64 (num_to_be_bytes n)
End

val () = cv_trans encode_fq_def;

(* Decode 128-byte Fq2 element: c0 (64 bytes) + c1 (64 bytes) = c0 + c1*u *)
Definition decode_fq2_def:
  decode_fq2 bytes =
    if LENGTH bytes ≠ 128 then NONE
    else case decode_fq (TAKE 64 bytes) of
           NONE => NONE
         | SOME c0 =>
           case decode_fq (DROP 64 bytes) of
             NONE => NONE
           | SOME c1 => SOME (c0, c1)
End

val () = cv_trans decode_fq2_def;

(* Encode Fq2 element to 128 bytes *)
Definition encode_fq2_def:
  encode_fq2 (c0, c1) = encode_fq c0 ++ encode_fq c1
End

val () = cv_trans encode_fq2_def;

(* Check if all bytes are zero *)
Definition all_zeros_def:
  all_zeros (bs : word8 list) =
    case bs of
      [] => T
    | (b::rest) => (b = 0w) ∧ all_zeros rest
End

val () = cv_trans all_zeros_def;

(* Check if G1 point (x, y) is on curve: y² = x³ + 4 *)
Definition g1_on_curve_def:
  g1_on_curve x y =
    (fmul y y = fadd (fmul x (fmul x x)) bls12381b)
End

val () = cv_trans g1_on_curve_def;

(* Decode 128-byte G1 point: x (64 bytes) + y (64 bytes) *)
(* All zeros = point at infinity *)
Definition decode_g1_def:
  decode_g1 bytes =
    if LENGTH bytes ≠ 128 then NONE
    else if all_zeros bytes then SOME g1_zero
    else case decode_fq (TAKE 64 bytes) of
           NONE => NONE
         | SOME x =>
           case decode_fq (DROP 64 bytes) of
             NONE => NONE
           | SOME y =>
             if g1_on_curve x y then SOME (x, y, 1n)
             else NONE
End

val () = cv_trans decode_g1_def;

(* Encode G1 point to 128 bytes *)
Definition encode_g1_def:
  encode_g1 p =
    let (x, y) = g1_to_affine p in
    if g1_is_inf p then REPLICATE 128 0w
    else encode_fq x ++ encode_fq y
End

val () = cv_trans encode_g1_def;

(* Check if G2 point (x, y) is on curve: y² = x³ + (4, 4) *)
Definition g2_on_curve_def:
  g2_on_curve x y =
    (f2mul y y = f2add (f2mul x (f2mul x x)) g2_b)
End

val () = cv_trans g2_on_curve_def;

(* Decode 256-byte G2 point: x (128 bytes as Fq2) + y (128 bytes as Fq2) *)
Definition decode_g2_def:
  decode_g2 bytes =
    if LENGTH bytes ≠ 256 then NONE
    else if all_zeros bytes then SOME g2_zero
    else case decode_fq2 (TAKE 128 bytes) of
           NONE => NONE
         | SOME x =>
           case decode_fq2 (DROP 128 bytes) of
             NONE => NONE
           | SOME y =>
             if g2_on_curve x y then SOME (x, y, f2one)
             else NONE
End

val () = cv_trans decode_g2_def;

(* Encode G2 point to 256 bytes *)
Definition encode_g2_def:
  encode_g2 p =
    let (x, y) = g2_to_affine p in
    if g2_is_inf p then REPLICATE 256 0w
    else encode_fq2 x ++ encode_fq2 y
End

val () = cv_trans encode_g2_def;

(* Subgroup check: P is in subgroup iff n * P = infinity *)
Definition g1_in_subgroup_def:
  g1_in_subgroup p = g1_is_inf (g1_mul p bls12381n)
End

val () = cv_trans g1_in_subgroup_def;

Definition g2_in_subgroup_def:
  g2_in_subgroup p = g2_is_inf (g2_mul p bls12381n)
End

val () = cv_trans g2_in_subgroup_def;

(* ============================================================ *)
(* Multi-Scalar Multiplication (MSM)                            *)
(* ============================================================ *)

(* Simple MSM: sum of scalar * point products *)
Definition g1_msm_def:
  g1_msm [] = g1_zero ∧
  g1_msm ((p, s)::rest) = g1_add (g1_mul p s) (g1_msm rest)
End

val () = cv_trans g1_msm_def;

Definition g2_msm_def:
  g2_msm [] = g2_zero ∧
  g2_msm ((p, s)::rest) = g2_add (g2_mul p s) (g2_msm rest)
End

val () = cv_trans g2_msm_def;

(* G1 MSM discount table per EIP-2537 *)
Definition g1_msm_discount_def:
  g1_msm_discount (k:num) =
    if k = 0 then 0n
    else if k = 1 then 1000n
    else if k = 2 then 949n
    else if k = 3 then 848n
    else if k = 4 then 797n
    else if k = 5 then 764n
    else if k = 6 then 750n
    else if k = 7 then 738n
    else if k = 8 then 728n
    else if k = 9 then 719n
    else if k = 10 then 712n
    else if k = 11 then 705n
    else if k = 12 then 698n
    else if k = 13 then 692n
    else if k = 14 then 687n
    else if k = 15 then 682n
    else if k = 16 then 677n
    else if k = 17 then 673n
    else if k = 18 then 669n
    else if k = 19 then 665n
    else if k = 20 then 661n
    else if k = 21 then 658n
    else if k = 22 then 654n
    else if k = 23 then 651n
    else if k = 24 then 648n
    else if k = 25 then 645n
    else if k = 26 then 642n
    else if k = 27 then 640n
    else if k = 28 then 637n
    else if k = 29 then 635n
    else if k = 30 then 632n
    else if k = 31 then 630n
    else if k = 32 then 627n
    else if k = 33 then 625n
    else if k = 34 then 623n
    else if k = 35 then 621n
    else if k = 36 then 619n
    else if k = 37 then 617n
    else if k = 38 then 615n
    else if k = 39 then 613n
    else if k = 40 then 611n
    else if k = 41 then 609n
    else if k = 42 then 608n
    else if k = 43 then 606n
    else if k = 44 then 604n
    else if k = 45 then 603n
    else if k = 46 then 601n
    else if k = 47 then 599n
    else if k = 48 then 598n
    else if k = 49 then 596n
    else if k = 50 then 595n
    else if k = 51 then 593n
    else if k = 52 then 592n
    else if k = 53 then 591n
    else if k = 54 then 589n
    else if k = 55 then 588n
    else if k = 56 then 586n
    else if k = 57 then 585n
    else if k = 58 then 584n
    else if k = 59 then 582n
    else if k = 60 then 581n
    else if k = 61 then 580n
    else if k = 62 then 579n
    else if k = 63 then 577n
    else if k = 64 then 576n
    else if k = 65 then 575n
    else if k = 66 then 574n
    else if k = 67 then 573n
    else if k = 68 then 572n
    else if k = 69 then 570n
    else if k = 70 then 569n
    else if k = 71 then 568n
    else if k = 72 then 567n
    else if k = 73 then 566n
    else if k = 74 then 565n
    else if k = 75 then 564n
    else if k = 76 then 563n
    else if k = 77 then 562n
    else if k = 78 then 561n
    else if k = 79 then 560n
    else if k = 80 then 559n
    else if k = 81 then 558n
    else if k = 82 then 557n
    else if k = 83 then 556n
    else if k = 84 then 555n
    else if k = 85 then 554n
    else if k = 86 then 553n
    else if k = 87 then 552n
    else if k = 88 then 551n
    else if k = 89 then 550n
    else if k = 90 then 549n
    else if k = 91 then 548n
    else if k = 92 then 547n
    else if k = 93 then 547n
    else if k = 94 then 546n
    else if k = 95 then 545n
    else if k = 96 then 544n
    else if k = 97 then 543n
    else if k = 98 then 542n
    else if k = 99 then 541n
    else if k = 100 then 540n
    else if k = 101 then 540n
    else if k = 102 then 539n
    else if k = 103 then 538n
    else if k = 104 then 537n
    else if k = 105 then 536n
    else if k = 106 then 536n
    else if k = 107 then 535n
    else if k = 108 then 534n
    else if k = 109 then 533n
    else if k = 110 then 532n
    else if k = 111 then 532n
    else if k = 112 then 531n
    else if k = 113 then 530n
    else if k = 114 then 529n
    else if k = 115 then 528n
    else if k = 116 then 528n
    else if k = 117 then 527n
    else if k = 118 then 526n
    else if k = 119 then 525n
    else if k = 120 then 525n
    else if k = 121 then 524n
    else if k = 122 then 523n
    else if k = 123 then 522n
    else if k = 124 then 522n
    else if k = 125 then 521n
    else if k = 126 then 520n
    else if k = 127 then 520n
    else if k = 128 then 519n
    else 519n
End

val () = cv_trans g1_msm_discount_def;

(* G2 MSM discount table per EIP-2537 *)
Definition g2_msm_discount_def:
  g2_msm_discount (k:num) =
    if k = 0 then 0n
    else if k = 1 then 1000n
    else if k = 2 then 1000n
    else if k = 3 then 923n
    else if k = 4 then 884n
    else if k = 5 then 855n
    else if k = 6 then 832n
    else if k = 7 then 812n
    else if k = 8 then 796n
    else if k = 9 then 782n
    else if k = 10 then 770n
    else if k = 11 then 759n
    else if k = 12 then 749n
    else if k = 13 then 740n
    else if k = 14 then 732n
    else if k = 15 then 724n
    else if k = 16 then 717n
    else if k = 17 then 711n
    else if k = 18 then 704n
    else if k = 19 then 699n
    else if k = 20 then 693n
    else if k = 21 then 688n
    else if k = 22 then 683n
    else if k = 23 then 679n
    else if k = 24 then 674n
    else if k = 25 then 670n
    else if k = 26 then 666n
    else if k = 27 then 663n
    else if k = 28 then 659n
    else if k = 29 then 655n
    else if k = 30 then 652n
    else if k = 31 then 649n
    else if k = 32 then 646n
    else if k = 33 then 643n
    else if k = 34 then 640n
    else if k = 35 then 637n
    else if k = 36 then 634n
    else if k = 37 then 632n
    else if k = 38 then 629n
    else if k = 39 then 627n
    else if k = 40 then 624n
    else if k = 41 then 622n
    else if k = 42 then 620n
    else if k = 43 then 618n
    else if k = 44 then 615n
    else if k = 45 then 613n
    else if k = 46 then 611n
    else if k = 47 then 609n
    else if k = 48 then 607n
    else if k = 49 then 606n
    else if k = 50 then 604n
    else if k = 51 then 602n
    else if k = 52 then 600n
    else if k = 53 then 598n
    else if k = 54 then 597n
    else if k = 55 then 595n
    else if k = 56 then 593n
    else if k = 57 then 592n
    else if k = 58 then 590n
    else if k = 59 then 589n
    else if k = 60 then 587n
    else if k = 61 then 586n
    else if k = 62 then 584n
    else if k = 63 then 583n
    else if k = 64 then 582n
    else if k = 65 then 580n
    else if k = 66 then 579n
    else if k = 67 then 578n
    else if k = 68 then 576n
    else if k = 69 then 575n
    else if k = 70 then 574n
    else if k = 71 then 573n
    else if k = 72 then 571n
    else if k = 73 then 570n
    else if k = 74 then 569n
    else if k = 75 then 568n
    else if k = 76 then 567n
    else if k = 77 then 566n
    else if k = 78 then 565n
    else if k = 79 then 563n
    else if k = 80 then 562n
    else if k = 81 then 561n
    else if k = 82 then 560n
    else if k = 83 then 559n
    else if k = 84 then 558n
    else if k = 85 then 557n
    else if k = 86 then 556n
    else if k = 87 then 555n
    else if k = 88 then 554n
    else if k = 89 then 553n
    else if k = 90 then 552n
    else if k = 91 then 552n
    else if k = 92 then 551n
    else if k = 93 then 550n
    else if k = 94 then 549n
    else if k = 95 then 548n
    else if k = 96 then 547n
    else if k = 97 then 546n
    else if k = 98 then 545n
    else if k = 99 then 545n
    else if k = 100 then 544n
    else if k = 101 then 543n
    else if k = 102 then 542n
    else if k = 103 then 541n
    else if k = 104 then 541n
    else if k = 105 then 540n
    else if k = 106 then 539n
    else if k = 107 then 538n
    else if k = 108 then 537n
    else if k = 109 then 537n
    else if k = 110 then 536n
    else if k = 111 then 535n
    else if k = 112 then 535n
    else if k = 113 then 534n
    else if k = 114 then 533n
    else if k = 115 then 532n
    else if k = 116 then 532n
    else if k = 117 then 531n
    else if k = 118 then 530n
    else if k = 119 then 530n
    else if k = 120 then 529n
    else if k = 121 then 528n
    else if k = 122 then 528n
    else if k = 123 then 527n
    else if k = 124 then 526n
    else if k = 125 then 526n
    else if k = 126 then 525n
    else if k = 127 then 524n
    else 524n
End

val () = cv_trans g2_msm_discount_def;

(* Decode G1 + scalar pair (160 bytes) *)
Definition decode_g1_scalar_def:
  decode_g1_scalar bytes =
    if LENGTH bytes ≠ 160 then NONE
    else case decode_g1 (TAKE 128 bytes) of
           NONE => NONE
         | SOME p =>
           let s = num_of_be_bytes (DROP 128 bytes) in
           SOME (p, s)
End

val () = cv_trans decode_g1_scalar_def;

(* Decode G2 + scalar pair (288 bytes) *)
Definition decode_g2_scalar_def:
  decode_g2_scalar bytes =
    if LENGTH bytes ≠ 288 then NONE
    else case decode_g2 (TAKE 256 bytes) of
           NONE => NONE
         | SOME p =>
           let s = num_of_be_bytes (DROP 256 bytes) in
           SOME (p, s)
End

val () = cv_trans decode_g2_scalar_def;

(* Decode list of G1+scalar pairs - tail-recursive version *)
Definition decode_g1_scalars_acc_def:
  decode_g1_scalars_acc acc bytes =
    if LENGTH bytes = 0 then SOME (REVERSE acc)
    else if LENGTH bytes < 160 then NONE
    else case decode_g1_scalar (TAKE 160 bytes) of
           NONE => NONE
         | SOME ps => decode_g1_scalars_acc (ps::acc) (DROP 160 bytes)
Termination
  WF_REL_TAC `measure (LENGTH o SND)`
  >> rw[] >> gvs[LENGTH_DROP]
End

val () = cv_trans decode_g1_scalars_acc_def;

Definition decode_g1_scalars_def:
  decode_g1_scalars bytes = decode_g1_scalars_acc [] bytes
End

val () = cv_trans decode_g1_scalars_def;

(* Decode list of G2+scalar pairs - tail-recursive version *)
Definition decode_g2_scalars_acc_def:
  decode_g2_scalars_acc acc bytes =
    if LENGTH bytes = 0 then SOME (REVERSE acc)
    else if LENGTH bytes < 288 then NONE
    else case decode_g2_scalar (TAKE 288 bytes) of
           NONE => NONE
         | SOME ps => decode_g2_scalars_acc (ps::acc) (DROP 288 bytes)
Termination
  WF_REL_TAC `measure (LENGTH o SND)`
  >> rw[] >> gvs[LENGTH_DROP]
End

val () = cv_trans decode_g2_scalars_acc_def;

Definition decode_g2_scalars_def:
  decode_g2_scalars bytes = decode_g2_scalars_acc [] bytes
End

val () = cv_trans decode_g2_scalars_def;

(* Check all pairs in MSM list are in subgroup *)
Definition g1_all_in_subgroup_def:
  g1_all_in_subgroup [] = T ∧
  g1_all_in_subgroup ((p, s)::rest) =
    (g1_in_subgroup p ∧ g1_all_in_subgroup rest)
End

val () = cv_trans g1_all_in_subgroup_def;

Definition g2_all_in_subgroup_def:
  g2_all_in_subgroup [] = T ∧
  g2_all_in_subgroup ((p, s)::rest) =
    (g2_in_subgroup p ∧ g2_all_in_subgroup rest)
End

val () = cv_trans g2_all_in_subgroup_def;

(* ============================================================ *)
(* Precompile Implementations (0x0b - 0x11)                     *)
(* ============================================================ *)

(* 0x0b: G1 Addition - no subgroup check required *)
Definition bls_g1add_def:
  bls_g1add input =
    if LENGTH input ≠ 256 then NONE
    else case decode_g1 (TAKE 128 input) of
           NONE => NONE
         | SOME p1 =>
           case decode_g1 (DROP 128 input) of
             NONE => NONE
           | SOME p2 => SOME (encode_g1 (g1_add p1 p2))
End

val () = cv_trans bls_g1add_def;

(* 0x0c: G1 MSM - requires subgroup check *)
Definition bls_g1msm_def:
  bls_g1msm input =
    if input = [] then NONE
    else if LENGTH input MOD 160 ≠ 0 then NONE
    else case decode_g1_scalars input of
           NONE => NONE
         | SOME pairs =>
           if ¬g1_all_in_subgroup pairs then NONE
           else SOME (encode_g1 (g1_msm pairs))
End

val () = cv_trans bls_g1msm_def;

(* 0x0d: G2 Addition - no subgroup check required *)
Definition bls_g2add_def:
  bls_g2add input =
    if LENGTH input ≠ 512 then NONE
    else case decode_g2 (TAKE 256 input) of
           NONE => NONE
         | SOME p1 =>
           case decode_g2 (DROP 256 input) of
             NONE => NONE
           | SOME p2 => SOME (encode_g2 (g2_add p1 p2))
End

val () = cv_trans bls_g2add_def;

(* 0x0e: G2 MSM - requires subgroup check *)
Definition bls_g2msm_def:
  bls_g2msm input =
    if input = [] then NONE
    else if LENGTH input MOD 288 ≠ 0 then NONE
    else case decode_g2_scalars input of
           NONE => NONE
         | SOME pairs =>
           if ¬g2_all_in_subgroup pairs then NONE
           else SOME (encode_g2 (g2_msm pairs))
End

val () = cv_trans bls_g2msm_def;

(* Decode G1+G2 pair for pairing (384 bytes) *)
Definition decode_pairing_pair_def:
  decode_pairing_pair bytes =
    if LENGTH bytes ≠ 384 then NONE
    else case decode_g1 (TAKE 128 bytes) of
           NONE => NONE
         | SOME p1 =>
           case decode_g2 (DROP 128 bytes) of
             NONE => NONE
           | SOME p2 => SOME (p1, p2)
End

val () = cv_trans decode_pairing_pair_def;

(* Decode list of G1+G2 pairs for pairing - tail-recursive version *)
Definition decode_pairing_pairs_acc_def:
  decode_pairing_pairs_acc acc bytes =
    if LENGTH bytes = 0 then SOME (REVERSE acc)
    else if LENGTH bytes < 384 then NONE
    else case decode_pairing_pair (TAKE 384 bytes) of
           NONE => NONE
         | SOME pair => decode_pairing_pairs_acc (pair::acc) (DROP 384 bytes)
Termination
  WF_REL_TAC `measure (LENGTH o SND)`
  >> rw[] >> gvs[LENGTH_DROP]
End

val () = cv_trans decode_pairing_pairs_acc_def;

Definition decode_pairing_pairs_def:
  decode_pairing_pairs bytes = decode_pairing_pairs_acc [] bytes
End

val () = cv_trans decode_pairing_pairs_def;

(* Check all pairing pairs are in subgroup *)
Definition pairing_pairs_in_subgroup_def:
  pairing_pairs_in_subgroup [] = T ∧
  pairing_pairs_in_subgroup ((p1, p2)::rest) =
    (g1_in_subgroup p1 ∧ g2_in_subgroup p2 ∧ pairing_pairs_in_subgroup rest)
End

val () = cv_trans pairing_pairs_in_subgroup_def;

(* Compute product of pairings - note: pairing takes G2 first, then G1 *)
Definition multi_pairing_def:
  multi_pairing [] = poly12_one ∧
  multi_pairing ((p1, p2)::rest) =
    poly12_mul (pairing p2 p1) (multi_pairing rest)
End

val () = cv_trans multi_pairing_def;

(* 0x0f: Pairing check - returns 1 if product of pairings = 1 *)
Definition bls_pairing_def:
  bls_pairing input =
    if input = [] then NONE
    else if LENGTH input MOD 384 ≠ 0 then NONE
    else case decode_pairing_pairs input of
           NONE => NONE
         | SOME pairs =>
           if ¬pairing_pairs_in_subgroup pairs then NONE
           else let result = multi_pairing pairs in
                let is_one = (result = poly12_one) in
                SOME (REPLICATE 31 (0w:word8) ++ [if is_one then 1w else 0w])
End

val () = cv_trans bls_pairing_def;

(* ============================================================ *)
(* Map to Curve (SWU Algorithm)                                 *)
(* ============================================================ *)

(* 11-isogeny constants for BLS12-381 G1 *)
(* A' and B' define the isogenous curve E': y² = x³ + A'x + B' *)
Definition iso_11_a_def:
  iso_11_a = 0x144698a3b8e9433d693a02c96d4982b0ea985383ee66a8d8e8981aefd881ac98936f8da0e0f97f5cf428082d584c1dn
End

Definition iso_11_b_def:
  iso_11_b = 0x12e2908d11688030018b12e8753eee3b2016c1f0f24f4070a0b9c14fcef35ef55a23215a316ceaa5d1cc48e98e172be0n
End

val () = cv_trans_deep_embedding EVAL iso_11_a_def;
val () = cv_trans_deep_embedding EVAL iso_11_b_def;

(* Z parameter for G1 SWU *)
Definition sswu_z_g1_def:
  sswu_z_g1 = 11n
End

val () = cv_trans_deep_embedding EVAL sswu_z_g1_def;

(* (p - 3) / 4 for square root computation *)
Definition p_minus_3_div_4_def:
  p_minus_3_div_4 = 0x680447a8e5ff9a692c6e9ed90d2eb35d91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaaan
End

val () = cv_trans_deep_embedding EVAL p_minus_3_div_4_def;

(* sqrt(-11³) for handling non-square case in SWU *)
Definition sqrt_minus_11_cubed_def:
  sqrt_minus_11_cubed = 0x3d689d1e0e762cef9f2bec6130316806b4c80eda6fc10ce77ae83eab1ea8b8b8a407c9c6db195e06f2dbeabc2baeff5n
End

val () = cv_trans_deep_embedding EVAL sqrt_minus_11_cubed_def;

(* Compute sqrt(u/v) if it exists, otherwise return a candidate *)
(* Returns (is_valid_root, result) *)
Definition sqrt_div_fq_def:
  sqrt_div_fq u v =
    let temp = fmul u v in
    let v2 = fmul v v in
    let temp_v2 = fmul temp v2 in
    let result = fmul temp (fexp temp_v2 p_minus_3_div_4) in
    let check = fsub (fmul (fmul result result) v) u in
    (check = 0, result)
End

val () = cv_trans sqrt_div_fq_def;

(* Sign of a field element (sgn0 from RFC 9380) *)
(* Returns the least significant bit *)
Definition fsgn0_def:
  fsgn0 x = x MOD 2
End

val () = cv_trans fsgn0_def;

(* 11-isogeny map coefficients for x coordinate *)
Definition iso_11_x_num_def:
  iso_11_x_num : num list = [
    0x11a05f2b1e833340b809101dd99815856b303e88a2d7005ff2627b56cdb4e2c85610c2d5f2e62d6eaeac1662734649b7n;
    0x17294ed3e943ab2f0588bab22147a81c7c17e75b2f6a8417f565e33c70d1e86b4838f2a6f318c356e834eef1b3cb83bbn;
    0xd54005db97678ec1d1048c5d10a9a1bce032473295983e56878e501ec68e25c958c3e3d2a09729fe0179f9dac9edcb0n;
    0x1778e7166fcc6db74e0609d307e55412d7f5e4656a8dbf25f1b33289f1b330835336e25ce3107193c5b388641d9b6861n;
    0xe99726a3199f4436642b4b3e4118e5499db995a1257fb3f086eeb65982fac18985a286f301e77c451154ce9ac8895d9n;
    0x1630c3250d7313ff01d1201bf7a74ab5db3cb17dd952799b9ed3ab9097e68f90a0870d2dcae73d19cd13c1c66f652983n;
    0xd6ed6553fe44d296a3726c38ae652bfb11586264f0f8ce19008e218f9c86b2a8da25128c1052ecaddd7f225a139ed84n;
    0x17b81e7701abdbe2e8743884d1117e53356de5ab275b4db1a682c62ef0f2753339b7c8f8c8f475af9ccb5618e3f0c88en;
    0x80d3cf1f9a78fc47b90b33563be990dc43b756ce79f5574a2c596c928c5d1de4fa295f296b74e956d71986a8497e317n;
    0x169b1f8e1bcfa7c42e0c37515d138f22dd2ecb803a0c5c99676314baf4bb1b7fa3190b2edc0327797f241067be390c9en;
    0x10321da079ce07e272d8ec09d2565b0dfa7dccdde6787f96d50af36003b14866f69b771f8c285decca67df3f1605fb7bn;
    0x6e08c248e260e70bd1e962381edee3d31d79d7e22c837bc23c0bf1bc24c6b68c24b1b80b64d391fa9c8ba2e8ba2d229n
  ]
End

Definition iso_11_x_den_def:
  iso_11_x_den : num list = [
    0x8ca8d548cff19ae18b2e62f4bd3fa6f01d5ef4ba35b48ba9c9588617fc8ac62b558d681be343df8993cf9fa40d21b1cn;
    0x12561a5deb559c4348b4711298e536367041e8ca0cf0800c0126c2588c48bf5713daa8846cb026e9e5c8276ec82b3bffn;
    0xb2962fe57a3225e8137e629bff2991f6f89416f5a718cd1fca64e00b11aceacd6a3d0967c94fedcfcc239ba5cb83e19n;
    0x3425581a58ae2fec83aafef7c40eb545b08243f16b1655154cca8abc28d6fd04976d5243eecf5c4130de8938dc62cd8n;
    0x13a8e162022914a80a6f1d5f43e7a07dffdfc759a12062bb8d6b44e833b306da9bd29ba81f35781d539d395b3532a21en;
    0xe7355f8e4e667b955390f7f0506c6e9395735e9ce9cad4d0a43bcef24b8982f7400d24bc4228f11c02df9a29f6304a5n;
    0x772caacf16936190f3e0c63e0596721570f5799af53a1894e2e073062aede9cea73b3538f0de06cec2574496ee84a3an;
    0x14a7ac2a9d64a8b230b3f5b074cf01996e7f63c21bca68a81996e1cdf9822c580fa5b9489d11e2d311f7d99bbdcc5a5en;
    0xa10ecf6ada54f825e920b3dafc7a3cce07f8d1d7161366b74100da67f39883503826692abba43704776ec3a79a1d641n;
    0x95fc13ab9e92ad4476d6e3eb3a56680f682b4ee96f7d03776df533978f31c1593174e4b4b7865002d6384d168ecdd0an;
    1n
  ]
End

Definition iso_11_y_num_def:
  iso_11_y_num : num list = [
    0x90d97c81ba24ee0259d1f094980dcfa11ad138e48a869522b52af6c956543d3cd0c7aee9b3ba3c2be9845719707bb33n;
    0x134996a104ee5811d51036d776fb46831223e96c254f383d0f906343eb67ad34d6c56711962fa8bfe097e75a2e41c696n;
    0xcc786baa966e66f4a384c86a3b49942552e2d658a31ce2c344be4b91400da7d26d521628b00523b8dfe240c72de1f6n;
    0x1f86376e8981c217898751ad8746757d42aa7b90eeb791c09e4a3ec03251cf9de405aba9ec61deca6355c77b0e5f4cbn;
    0x8cc03fdefe0ff135caf4fe2a21529c4195536fbe3ce50b879833fd221351adc2ee7f8dc099040a841b6daecf2e8fedbn;
    0x16603fca40634b6a2211e11db8f0a6a074a7d0d4afadb7bd76505c3d3ad5544e203f6326c95a807299b23ab13633a5f0n;
    0x4ab0b9bcfac1bbcb2c977d027796b3ce75bb8ca2be184cb5231413c4d634f3747a87ac2460f415ec961f8855fe9d6f2n;
    0x987c8d5333ab86fde9926bd2ca6c674170a05bfe3bdd81ffd038da6c26c842642f64550fedfe935a15e4ca31870fb29n;
    0x9fc4018bd96684be88c9e221e4da1bb8f3abd16679dc26c1e8b6e6a1f20cabe69d65201c78607a360370e577bdba587n;
    0xe1bba7a1186bdb5223abde7ada14a23c42a0ca7915af6fe06985e7ed1e4d43b9b3f7055dd4eba6f2bafaaebca731c30n;
    0x19713e47937cd1be0dfd0b8f1d43fb93cd2fcbcb6caf493fd1183e416389e61031bf3a5cce3fbafce813711ad011c132n;
    0x18b46a908f36f6deb918c143fed2edcc523559b8aaf0c2462e6bfe7f911f643249d9cdf41b44d606ce07c8a4d0074d8en;
    0xb182cac101b9399d155096004f53f447aa7b12a3426b08ec02710e807b4633f06c851c1919211f20d4c04f00b971ef8n;
    0x245a394ad1eca9b72fc00ae7be315dc757b3b080d4c158013e6632d3c40659cc6cf90ad1c232a6442d9d3f5db980133n;
    0x5c129645e44cf1102a159f748c4a3fc5e673d81d7e86568d9ab0f5d396a7ce46ba1049b6579afb7866b1e715475224bn;
    0x15e6be4e990f03ce4ea50b3b42df2eb5cb181d8f84965a3957add4fa95af01b2b665027efec01c7704b456be69c8b604n
  ]
End

Definition iso_11_y_den_def:
  iso_11_y_den : num list = [
    0x16112c4c3a9c98b252181140fad0eae9601a6de578980be6eec3232b5be72e7a07f3688ef60c206d01479253b03663c1n;
    0x1962d75c2381201e1a0cbd6c43c348b885c84ff731c4d59ca4a10356f453e01f78a4260763529e3532f6102c2e49a03dn;
    0x58df3306640da276faaae7d6e8eb15778c4855551ae7f310c35a5dd279cd2eca6757cd636f96f891e2538b53dbf67f2n;
    0x16b7d288798e5395f20d23bf89edb4d1d115c5dbddbcd30e123da489e726af41727364f2c28297ada8d26d98445f5416n;
    0xbe0e079545f43e4b00cc912f8228ddcc6d19c9f0f69bbb0542eda0fc9dec916a20b15dc0fd2ededda39142311a5001dn;
    0x8d9e5297186db2d9fb266eaac783182b70152c65550d881c5ecd87b6f0f5a6449f38db9dfa9cce202c6477faaf9b7acn;
    0x166007c08a99db2fc3ba8734ace9824b5eecfdfa8d0cf8ef5dd365bc400a0051d5fa9c01a58b1fb93d1a1399126a775cn;
    0x16a3ef08be3ea7ea03bcddfabba6ff6ee5a4375efa1f4fd7feb34fd206357132b920f5b00801dee460ee415a15812ed9n;
    0x1866c8ed336c61231a1be54fd1d74cc4f9fb0ce4c6af5920abc5750c4bf39b4852cfe2f7bb9248836b233d9d55535d4an;
    0x167a55cda70a6e1cea820597d94a84903216f763e13d87bb5308592e7ea7d4fbc7385ea3d529b35e346ef48bb8913f55n;
    0x4d2f259eea405bd48f010a01ad2911d9c6dd039bb61a6290e591b36e636a5c871a5c29f4f83060400f8b49cba8f6aa8n;
    0xaccbb67481d033ff5852c1e48c50c477f94ff8aefce42d28c0f9a88cea7913516f968986f7ebbea9684b529e2561092n;
    0xad6b9514c767fe3c3613144b45f1496543346d98adf02267d5ceef9a00d9b8693000763e3b90ac11e99b138573345ccn;
    0x2660400eb2e4f3b628bdd0d53cd76f2bf565b94e72927c1cb748df27942480e420517bd8714cc80d1fadc1326ed06f7n;
    0xe0fa1d816ddc03e6b24255e0d7819c171c40f65e273b853324efcd6356caa205ca2f570f13497804415473a1d634b8fn;
    1n
  ]
End

val () = cv_trans_deep_embedding EVAL iso_11_x_num_def;
val () = cv_trans_deep_embedding EVAL iso_11_x_den_def;
val () = cv_trans_deep_embedding EVAL iso_11_y_num_def;
val () = cv_trans_deep_embedding EVAL iso_11_y_den_def;

(* Evaluate polynomial using Horner's method with z-scaling *)
(* For coeffs [c0, c1, ..., cn] and z_powers [z, z^2, ..., z^15], computes: *)
(* c_n * x^n + c_{n-1} * z * x^{n-1} + ... + c_0 * z^n *)
(* Result is z^n * P(x/z) for polynomial P *)
Definition eval_iso_poly_def:
  eval_iso_poly acc [] z_powers x = acc ∧
  eval_iso_poly acc (c::cs) [] x = eval_iso_poly (fadd (fmul acc x) c) cs [] x ∧
  eval_iso_poly acc (c::cs) (z::zs) x =
    eval_iso_poly (fadd (fmul acc x) (fmul z c)) cs zs x
End

val () = cv_trans eval_iso_poly_def;

(* 11-isogeny map from E' to E for G1 *)
(* Maps (x', y', z') on isogenous curve to (x, y, z) on BLS12-381 *)
(* Algorithm from Section 4 of https://eprint.iacr.org/2019/403 *)
Definition iso_map_g1_def:
  iso_map_g1 (x', y', z') =
    (* Compute powers of z' *)
    let z2 = fmul z' z' in
    let z3 = fmul z2 z' in
    let z4 = fmul z2 z2 in
    let z5 = fmul z4 z' in
    let z6 = fmul z3 z3 in
    let z7 = fmul z6 z' in
    let z8 = fmul z4 z4 in
    let z9 = fmul z8 z' in
    let z10 = fmul z5 z5 in
    let z11 = fmul z10 z' in
    let z12 = fmul z6 z6 in
    let z13 = fmul z12 z' in
    let z14 = fmul z7 z7 in
    let z15 = fmul z14 z' in
    let z_powers = [z'; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14; z15] in
    (* Evaluate polynomials using Horner with z-scaling *)
    (* x_num has 12 coeffs, x_den has 11, y_num/y_den have 16 *)
    (* Start with last coeff (EL 11/10/15), iterate through rest *)
    let x_num = eval_iso_poly (EL 11 iso_11_x_num) (REVERSE (TAKE 11 iso_11_x_num)) z_powers x' in
    let x_den = eval_iso_poly (EL 10 iso_11_x_den) (REVERSE (TAKE 10 iso_11_x_den)) z_powers x' in
    let y_num = eval_iso_poly (EL 15 iso_11_y_num) (REVERSE (TAKE 15 iso_11_y_num)) z_powers x' in
    let y_den = eval_iso_poly (EL 15 iso_11_y_den) (REVERSE (TAKE 15 iso_11_y_den)) z_powers x' in
    (* Apply corrections: x_den * z (degree is 1 less than x_num) *)
    let x_den = fmul x_den z' in
    (* y_num * y', y_den * z *)
    let y_num = fmul y_num y' in
    let y_den = fmul y_den z' in
    (* Result in projective coordinates *)
    let z_out = fmul x_den y_den in
    let x_out = fmul x_num y_den in
    let y_out = fmul y_num x_den in
    (x_out, y_out, z_out)
End

val iso_map_g1_pre_def = cv_trans_pre "iso_map_g1_pre" iso_map_g1_def;

Theorem iso_map_g1_pre[cv_pre]:
  ∀v. iso_map_g1_pre v
Proof
  Cases \\ Cases_on `r`
  \\ rw[iso_map_g1_pre_def]
  \\ EVAL_TAC
QED

(* Optimized SWU map for Fq to G1' (isogenous curve) *)
(* Based on Section 4 of https://eprint.iacr.org/2019/403 *)
(* Returns projective point (x, y, z) on the isogenous curve E' *)
Definition sswu_g1_def:
  sswu_g1 t =
    let z = sswu_z_g1 in
    let a = iso_11_a in
    let b = iso_11_b in
    (* t2 = t² *)
    let t2 = fmul t t in
    (* iso_11_z_t2 = Z * t² *)
    let z_t2 = fmul z t2 in
    (* temp = Z*t² + Z²*t⁴ *)
    let temp = fadd z_t2 (fmul z_t2 z_t2) in
    (* denominator = -A * temp *)
    let denom = fneg (fmul a temp) in
    (* numerator = B * (temp + 1) *)
    let numer = fmul b (fadd temp 1) in
    (* Handle exceptional case: if denom = 0, denom = Z * A *)
    let denom = if denom = 0 then fmul z a else denom in
    (* v = denom³ *)
    let denom2 = fmul denom denom in
    let v = fmul denom2 denom in
    (* u = numer³ + A * numer * denom² + B * v *)
    let numer2 = fmul numer numer in
    let numer3 = fmul numer2 numer in
    let u = fadd numer3 (fadd (fmul a (fmul numer denom2)) (fmul b v)) in
    (* Attempt y = sqrt(u / v) *)
    let (is_root, y_cand) = sqrt_div_fq u v in
    (* If not a valid root, adjust y and numer *)
    let (y, numer) = if is_root then (y_cand, numer)
                     else (fmul (fmul y_cand (fmul t2 t)) sqrt_minus_11_cubed,
                           fmul numer z_t2) in
    (* Adjust sign of y based on sgn0 *)
    let y = if fsgn0 t ≠ fsgn0 y then fneg y else y in
    (* Final y = y * denom *)
    let y = fmul y denom in
    (numer, y, denom)
End

val () = cv_trans sswu_g1_def;

(* 0x10: Map Fp to G1 *)
Definition bls_map_fp_to_g1_def:
  bls_map_fp_to_g1 input =
    if LENGTH input ≠ 64 then NONE
    else case decode_fq input of
           NONE => NONE
         | SOME u =>
             let p = sswu_g1 u in
             (* Apply 11-isogeny map to get point on BLS12-381 curve *)
             let p_mapped = iso_map_g1 p in
             (* Clear cofactor to get point in correct subgroup *)
             let h_eff = 15132376222941642753n in
             SOME (encode_g1 (g1_mul p_mapped h_eff))
End

val () = cv_trans bls_map_fp_to_g1_def;

(* ============================================================ *)
(* Map to G2 Curve (SWU Algorithm + 3-Isogeny)                  *)
(* ============================================================ *)

(* 3-isogeny constants for BLS12-381 G2 *)
(* Isogenous curve E': y^2 = x^3 + A'x + B' over Fq2 *)
Definition iso_3_a_def:
  iso_3_a : num # num = (0n, 240n)
End

Definition iso_3_b_def:
  iso_3_b : num # num = (1012n, 1012n)
End

(* Z = -2 - i = (p-2, p-1) *)
Definition iso_3_z_def:
  iso_3_z : num # num = (fsub 0 2n, fsub 0 1n)
End

val () = cv_trans_deep_embedding EVAL iso_3_a_def;
val () = cv_trans_deep_embedding EVAL iso_3_b_def;
val () = cv_trans_deep_embedding EVAL iso_3_z_def;

(* (p^2 - 9) / 16 for Fq2 square root *)
Definition p2_minus_9_div_16_def:
  p2_minus_9_div_16 = 1001205140483106588246484290269935788605945006208159541241399033561623546780709821462541004956387089373434649096260670658193992783731681621012512651314777238193313314641988297376025498093520728838658813979860931248214124593092835n
End

val () = cv_trans_deep_embedding EVAL p2_minus_9_div_16_def;

(* 8th roots of unity for Fq2 square root *)
Definition roots_of_unity_8_def:
  roots_of_unity_8 : (num # num) list = [
    (1n, 0n);
    (0n, 1n);
    (1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257n,
     1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257n);
    (1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257n,
     2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530n)
  ]
End

val () = cv_trans_deep_embedding EVAL roots_of_unity_8_def;

(* ETAS for handling non-square case in Fq2 SWU *)
Definition etas_g2_def:
  etas_g2 : (num # num) list = [
    (1015919005498129635886032702454337503112659152043614931979881174103627376789972962005013361970813319613593700736144n,
     1244231661155348484223428017511856347821538750986231559855759541903146219579071812422210818684355842447591283616181n);
    (2758177894066318909194361808224047808735344068952776325476298594220885430911766052020476810444659821590302988943606n,
     1015919005498129635886032702454337503112659152043614931979881174103627376789972962005013361970813319613593700736144n);
    (1646015993121829755895883253076789309308090876275172350194834453434199515639474951814226234213676147507404483718679n,
     1637752706019426886789797193293828301565549384974986623510918743054325021588194075665960171838131772227885159387073n);
    (2364656849202240506627992632442075854991333434964021261821139393069706628902643788776727457290883891810009113172714n,
     1646015993121829755895883253076789309308090876275172350194834453434199515639474951814226234213676147507404483718679n)
  ]
End

val () = cv_trans_deep_embedding EVAL etas_g2_def;

(* h_eff for G2 cofactor clearing *)
Definition h_eff_g2_def:
  h_eff_g2 = 209869847837335686905080341498658477663839067235703451875306851526599783796572738804459333109033834234622528588876978987822447936461846631641690358257586228683615991308971558879306463436166481n
End

val () = cv_trans_deep_embedding EVAL h_eff_g2_def;

(* 3-isogeny map coefficients for x numerator *)
Definition iso_3_x_num_def:
  iso_3_x_num : (num # num) list = [
    (889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235542n,
     889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235542n);
    (0n, 2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706522n);
    (2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706526n,
     1334136518407222464472596608578634718852294273313002628444019378708010550163612621480895876376338554679298090853261n);
    (3557697382419259905260257622876359250272784728834673675850718343221361467102966990615722337003569479144794908942033n, 0n)
  ]
End

(* 3-isogeny map coefficients for x denominator *)
Definition iso_3_x_den_def:
  iso_3_x_den : (num # num) list = [
    (0n, 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559715n);
    (12n, 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559775n);
    (1n, 0n)
  ]
End

(* 3-isogeny map coefficients for y numerator *)
Definition iso_3_y_num_def:
  iso_3_y_num : (num # num) list = [
    (3261222600550988246488569487636662646083386001431784202863158481286248011511053074731078808919938689216061999863558n,
     3261222600550988246488569487636662646083386001431784202863158481286248011511053074731078808919938689216061999863558n);
    (0n, 889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235518n);
    (2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706524n,
     1334136518407222464472596608578634718852294273313002628444019378708010550163612621480895876376338554679298090853263n);
    (2816510427748580758331037284777117739799287910327449993381818688383577828123182200904113516794492504322962636245776n, 0n)
  ]
End

(* 3-isogeny map coefficients for y denominator *)
Definition iso_3_y_den_def:
  iso_3_y_den : (num # num) list = [
    (4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559355n,
     4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559355n);
    (0n, 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559571n);
    (18n, 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559769n);
    (1n, 0n)
  ]
End

val () = cv_trans_deep_embedding EVAL iso_3_x_num_def;
val () = cv_trans_deep_embedding EVAL iso_3_x_den_def;
val () = cv_trans_deep_embedding EVAL iso_3_y_num_def;
val () = cv_trans_deep_embedding EVAL iso_3_y_den_def;

(* Find valid square root in Fq2 by trying 8th roots of unity *)
Definition find_sqrt_fq2_def:
  find_sqrt_fq2 gamma u v [] = (F, gamma) /\
  find_sqrt_fq2 gamma u v (root::roots) =
    let candidate = f2mul root gamma in
    let check = f2sub (f2mul (f2mul candidate candidate) v) u in
    if f2eq check f2zero then (T, candidate)
    else find_sqrt_fq2 gamma u v roots
End

val () = cv_trans find_sqrt_fq2_def;

(* Square root division in Fq2: compute sqrt(u/v) if it exists *)
(* Returns (is_valid, result) where result * result * v = u if valid *)
Definition sqrt_div_fq2_def:
  sqrt_div_fq2 u v =
    (* gamma = uv^7 * (uv^15)^((p^2-9)/16) *)
    let v2 = f2mul v v in
    let v3 = f2mul v2 v in
    let v4 = f2mul v2 v2 in
    let v7 = f2mul v4 v3 in
    let v8 = f2mul v4 v4 in
    let v15 = f2mul v8 v7 in
    let temp1 = f2mul u v7 in
    let temp2 = f2mul temp1 v8 in
    let gamma = f2mul (f2exp temp2 p2_minus_9_div_16) temp1 in
    find_sqrt_fq2 gamma u v roots_of_unity_8
End

val () = cv_trans sqrt_div_fq2_def;

(* Find valid eta for non-square case in Fq2 SWU *)
Definition find_eta_fq2_def:
  find_eta_fq2 sqrt_cand u v [] = sqrt_cand /\
  find_eta_fq2 sqrt_cand u v (eta::etas) =
    let candidate = f2mul eta sqrt_cand in
    let check = f2sub (f2mul (f2mul candidate candidate) v) u in
    if f2eq check f2zero then candidate
    else find_eta_fq2 sqrt_cand u v etas
End

val () = cv_trans find_eta_fq2_def;

(* Evaluate polynomial over Fq2 using Horner's method with z-scaling *)
Definition eval_iso_poly_fq2_def:
  eval_iso_poly_fq2 acc [] z_powers x = acc /\
  eval_iso_poly_fq2 acc (c::cs) [] x = eval_iso_poly_fq2 (f2add (f2mul acc x) c) cs [] x /\
  eval_iso_poly_fq2 acc (c::cs) (z::zs) x =
    eval_iso_poly_fq2 (f2add (f2mul acc x) (f2mul z c)) cs zs x
End

val () = cv_trans eval_iso_poly_fq2_def;

(* 3-isogeny map from E' to E for G2 *)
(* Maps (x', y', z') on isogenous curve to (x, y, z) on BLS12-381 G2 *)
Definition iso_map_g2_def:
  iso_map_g2 (x', y', z') =
    (* Compute powers of z' *)
    let z2 = f2mul z' z' in
    let z3 = f2mul z2 z' in
    let z_powers = [z'; z2; z3] in
    (* Evaluate polynomials using Horner with z-scaling *)
    (* x_num has degree 3, x_den has degree 2, y_num has degree 3, y_den has degree 3 *)
    let x_num = eval_iso_poly_fq2 (EL 3 iso_3_x_num) (REVERSE (TAKE 3 iso_3_x_num)) z_powers x' in
    let x_den = eval_iso_poly_fq2 (EL 2 iso_3_x_den) (REVERSE (TAKE 2 iso_3_x_den)) z_powers x' in
    let y_num = eval_iso_poly_fq2 (EL 3 iso_3_y_num) (REVERSE (TAKE 3 iso_3_y_num)) z_powers x' in
    let y_den = eval_iso_poly_fq2 (EL 3 iso_3_y_den) (REVERSE (TAKE 3 iso_3_y_den)) z_powers x' in
    (* Correct for x_den being 1 degree less than x_num *)
    let x_den = f2mul x_den z' in
    (* y_num * y', y_den * z *)
    let y_num = f2mul y_num y' in
    let y_den = f2mul y_den z' in
    (* Result in projective coordinates *)
    let z_out = f2mul x_den y_den in
    let x_out = f2mul x_num y_den in
    let y_out = f2mul y_num x_den in
    (x_out, y_out, z_out)
End

val iso_map_g2_pre_def = cv_trans_pre "iso_map_g2_pre" iso_map_g2_def;

Theorem iso_map_g2_pre[cv_pre]:
  !v. iso_map_g2_pre v
Proof
  Cases \\ Cases_on `r`
  \\ rw[iso_map_g2_pre_def]
  \\ EVAL_TAC
QED

(* Optimized SWU map for Fq2 to G2' (3-isogenous curve) *)
(* Returns projective point (x, y, z) on the isogenous curve E' *)
Definition sswu_g2_def:
  sswu_g2 u =
    let z = iso_3_z in
    let a = iso_3_a in
    let b = iso_3_b in
    (* t2 = u^2 *)
    let t2 = f2mul u u in
    (* z_t2 = Z * u^2 *)
    let z_t2 = f2mul z t2 in
    (* temp = Z*u^2 + Z^2*u^4 *)
    let temp = f2add z_t2 (f2mul z_t2 z_t2) in
    (* denominator = -A * temp *)
    let denom = f2neg (f2mul a temp) in
    (* numerator = B * (temp + 1) *)
    let numer = f2mul b (f2add temp f2one) in
    (* Handle exceptional case: if denom = 0, denom = Z * A *)
    let denom = if f2eq denom f2zero then f2mul z a else denom in
    (* v = denom^3 *)
    let denom2 = f2mul denom denom in
    let v = f2mul denom2 denom in
    (* curve_u = numer^3 + A * numer * denom^2 + B * v *)
    let numer2 = f2mul numer numer in
    let numer3 = f2mul numer2 numer in
    let curve_u = f2add numer3 (f2add (f2mul a (f2mul numer denom2)) (f2mul b v)) in
    (* Attempt y = sqrt(curve_u / v) *)
    let (is_root, y_cand) = sqrt_div_fq2 curve_u v in
    (* If not a valid root, handle non-square case *)
    let sqrt_cand = f2mul y_cand (f2mul t2 u) in  (* sqrt_cand * t^3 *)
    let u_new = f2mul (f2mul z_t2 (f2mul z_t2 z_t2)) curve_u in  (* Z^3 * t^6 * u *)
    let y_eta = find_eta_fq2 sqrt_cand u_new v etas_g2 in
    let (y, numer) = if is_root then (y_cand, numer)
                     else (y_eta, f2mul numer z_t2) in
    (* Adjust sign of y based on sgn0 *)
    let y = if f2sgn0 u <> f2sgn0 y then f2neg y else y in
    (* Final y = y * denom *)
    let y = f2mul y denom in
    (numer, y, denom)
End

val () = cv_trans sswu_g2_def;

(* 0x11: Map Fp2 to G2 *)
(* Includes cofactor clearing per EELS reference implementation *)
Definition bls_map_fp2_to_g2_def:
  bls_map_fp2_to_g2 input =
    if LENGTH input <> 128 then NONE
    else case decode_fq2 input of
           NONE => NONE
         | SOME u =>
             let p = sswu_g2 u in
             (* Apply 3-isogeny map to get point on BLS12-381 G2 curve *)
             let p_mapped = iso_map_g2 p in
             (* Clear cofactor to get point in correct subgroup *)
             SOME (encode_g2 (g2_mul p_mapped h_eff_g2))
End

val () = cv_trans bls_map_fp2_to_g2_def;
