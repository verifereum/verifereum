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
(* If we have coefficient c at position 12+k, it contributes:
   c * w^(12+k) = c * (2*w^6 - 2) * w^k = 2*c*w^(6+k) - 2*c*w^k *)
Definition poly12_reduce_def:
  poly12_reduce (c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,
                 c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22) =
  let
    (* w^12 = 2*w^6 - 2, so c12*w^12 -> 2*c12*w^6 - 2*c12 *)
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
    (* w^18 = 2*w^12 - 2*w^6 = 2*(2*w^6-2) - 2*w^6 = 2*w^6 - 4 *)
    (* Actually easier: c18*w^18 -> reduce c18*w^6 first, then the c12 terms *)
    r0 = fsub r0 (fmul 2 c18);
    r6 = fadd r6 (fmul 2 c18);
    r1 = fsub r1 (fmul 2 c19);
    r7 = fadd r7 (fmul 2 c19);
    r2 = fsub r2 (fmul 2 c20);
    r8 = fadd r8 (fmul 2 c20);
    r3 = fsub r3 (fmul 2 c21);
    r9 = fadd r9 (fmul 2 c21);
    r4 = fsub r4 (fmul 2 c22);
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
(* Polynomial inverse via extended Euclidean algorithm          *)
(* ============================================================ *)

Definition poly12_to_list_def:
  poly12_to_list (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11) =
  [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11]
End

val () = cv_trans poly12_to_list_def;

(* Helper to safely get element from list *)
Definition safe_el_def:
  safe_el n [] = 0n /\
  safe_el 0 (x::xs) = x /\
  safe_el (SUC n) (x::xs) = safe_el n xs
End

val () = cv_trans safe_el_def;

Definition list_to_poly12_def:
  list_to_poly12 xs =
  (safe_el 0 xs, safe_el 1 xs, safe_el 2 xs, safe_el 3 xs,
   safe_el 4 xs, safe_el 5 xs, safe_el 6 xs, safe_el 7 xs,
   safe_el 8 xs, safe_el 9 xs, safe_el 10 xs, safe_el 11 xs)
End

val () = cv_trans list_to_poly12_def;

(* Modulus polynomial for Fq12: w^12 - 2*w^6 + 2 *)
(* Represented as list [2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 1] *)
(* But we work with positive coefficients: [2, 0, 0, 0, 0, 0, p-2, 0, 0, 0, 0, 0, 1] *)
Definition poly12_modulus_list_def:
  poly12_modulus_list = [2n; 0; 0; 0; 0; 0;
    4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559785n;
    0; 0; 0; 0; 0; 1]
End

val () = cv_trans_deep_embedding EVAL poly12_modulus_list_def;

Definition poly_deg_def:
  poly_deg [] = 0 /\
  poly_deg (x::xs) = if EVERY (\c. c = 0) xs then (if x = 0 then 0 else 0)
                     else SUC (poly_deg xs)
End

Definition poly_lead_def:
  poly_lead [] = 0n /\
  poly_lead [x] = x /\
  poly_lead (x::xs) = poly_lead xs
End

val () = cv_trans poly_lead_def;

Definition poly_add_list_def:
  poly_add_list [] ys = ys /\
  poly_add_list xs [] = xs /\
  poly_add_list (x::xs) (y::ys) = fadd x y :: poly_add_list xs ys
End

val () = cv_trans poly_add_list_def;

(* Negate a list of field elements *)
Definition poly_neg_list_def:
  poly_neg_list [] = [] /\
  poly_neg_list (x::xs) = fneg x :: poly_neg_list xs
End

val () = cv_trans poly_neg_list_def;

Definition poly_sub_list_def:
  poly_sub_list [] ys = poly_neg_list ys /\
  poly_sub_list xs [] = xs /\
  poly_sub_list (x::xs) (y::ys) = fsub x y :: poly_sub_list xs ys
End

val () = cv_trans poly_sub_list_def;

Definition poly_scale_list_def:
  poly_scale_list s [] = [] /\
  poly_scale_list s (x::xs) = fmul s x :: poly_scale_list s xs
End

val () = cv_trans poly_scale_list_def;

(* Generate a list of n zeros *)
Definition zeros_def:
  zeros 0 = [] /\
  zeros (SUC n) = 0n :: zeros n
End

val () = cv_trans zeros_def;

Definition poly_shift_def:
  poly_shift n xs = zeros n ++ xs
End

val () = cv_trans poly_shift_def;

(* Drop leading zeros from a reversed list *)
Definition drop_leading_zeros_def:
  drop_leading_zeros [] = [] /\
  drop_leading_zeros (x::xs) = if x = 0n then drop_leading_zeros xs else (x::xs)
End

val () = cv_trans drop_leading_zeros_def;

Definition poly_trim_def:
  poly_trim xs = REVERSE (drop_leading_zeros (REVERSE xs))
End

val () = cv_trans poly_trim_def;

(* For FQ12 inverse, we use the fact that for a pairing target group element f,
   f^(-1) = conj(f) / |f|^2 where conj is conjugation in the extension field.
   However, for the miller loop we track numerator and denominator separately
   and compute f = num/den at the end using the conjugation trick. *)

(* Simpler Fq12 inverse using conjugation: f^(-1) = conj(f) * |f|^(-2)
   But for now, we'll skip this and handle division differently in miller loop *)
Definition poly12_inv_placeholder_def:
  poly12_inv_placeholder p = p (* placeholder - real inverse needed later *)
End

val () = cv_trans poly12_inv_placeholder_def;

Definition poly12_div_def:
  poly12_div x y = poly12_mul x (poly12_inv_placeholder y)
End

val () = cv_trans poly12_div_def;

(* ============================================================ *)
(* Twist: Embedding G2 points into Fq12                         *)
(* ============================================================ *)

(* Field isomorphism from Fq2 to Fq12 subfield *)
(* For BLS12-381: twist maps (x, y) in Fq2 to Fq12 *)
(* x -> x0*w + x1*w^7 (coefficients 1 and 7) *)
(* y -> y0 + y1*w^6 (coefficients 0 and 6) *)
(* z -> z0*w^3 + z1*w^9 (coefficients 3 and 9) *)
Definition twist_def:
  twist ((x0, x1), (y0, y1), (z0, z1)) =
  let
    (* Field isomorphism: (a + b*u) -> (a - b) + b*w^6 in appropriate embedding *)
    xc0 = fsub x0 x1;
    xc1 = x1;
    yc0 = fsub y0 y1;
    yc1 = y1;
    zc0 = fsub z0 z1;
    zc1 = z1
  in
  (* nx has coeffs at positions 1 and 7 *)
  (* ny has coeffs at positions 0 and 6 *)
  (* nz has coeffs at positions 3 and 9 *)
  (( 0n, xc0, 0n, 0n, 0n, 0n, 0n, xc1, 0n, 0n, 0n, 0n),
   (yc0, 0n, 0n, 0n, 0n, 0n, yc1, 0n, 0n, 0n, 0n, 0n),
   ( 0n, 0n, 0n, zc0, 0n, 0n, 0n, 0n, 0n, zc1, 0n, 0n))
End

val () = cv_trans twist_def;

(* Cast G1 point to Fq12 *)
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

Definition poly12_linefunc_def:
  poly12_linefunc (x1, y1, z1) (x2, y2, z2) (xt, yt, zt) =
  let
    m_num = poly12_sub (poly12_mul y2 z1) (poly12_mul y1 z2);
    m_den = poly12_sub (poly12_mul x2 z1) (poly12_mul x1 z2)
  in
    if m_den = poly12_zero then
      if m_num = poly12_zero then
        (* Tangent line: m = 3x^2 / 2y *)
        let
          m_num = poly12_scale 3 (poly12_sqr x1);
          m_den = poly12_scale 2 (poly12_mul y1 z1)
        in
          (poly12_sub (poly12_mul m_num (poly12_sub (poly12_mul xt z1) (poly12_mul x1 zt)))
                      (poly12_mul m_den (poly12_sub (poly12_mul yt z1) (poly12_mul y1 zt))),
           poly12_mul m_den (poly12_mul zt z1))
      else
        (* Vertical line *)
        (poly12_sub (poly12_mul xt z1) (poly12_mul x1 zt),
         poly12_mul z1 zt)
    else
      (* Secant line *)
      (poly12_sub (poly12_mul m_num (poly12_sub (poly12_mul xt z1) (poly12_mul x1 zt)))
                  (poly12_mul m_den (poly12_sub (poly12_mul yt z1) (poly12_mul y1 zt))),
       poly12_mul m_den (poly12_mul zt z1))
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

Definition log_ate_loop_count_def:
  log_ate_loop_count = 63n
End

val () = cv_trans log_ate_loop_count_def;

(* Fq12 point doubling for twisted points *)
Definition fq12_point_double_def:
  fq12_point_double (x, y, z) =
  if z = poly12_zero then (poly12_one, poly12_one, poly12_zero)
  else if y = poly12_zero then (poly12_one, poly12_one, poly12_zero)
  else let
    w = poly12_scale 3 (poly12_sqr x);
    s = poly12_mul y z;
    b = poly12_mul x (poly12_mul y s);
    h = poly12_sub (poly12_sqr w) (poly12_scale 8 b);
    s_sq = poly12_sqr s;
    x3 = poly12_scale 2 (poly12_mul h s);
    y3 = poly12_sub (poly12_mul w (poly12_sub (poly12_scale 4 b) h))
                    (poly12_scale 8 (poly12_mul (poly12_sqr y) s_sq));
    z3 = poly12_scale 8 (poly12_mul s s_sq)
  in (x3, y3, z3)
End

val () = cv_trans fq12_point_double_def;

(* Fq12 point addition for twisted points *)
Definition fq12_point_add_def:
  fq12_point_add (x1, y1, z1) (x2, y2, z2) =
  if z1 = poly12_zero then (x2, y2, z2)
  else if z2 = poly12_zero then (x1, y1, z1)
  else let
    u1 = poly12_mul y2 z1;
    u2 = poly12_mul y1 z2;
    v1 = poly12_mul x2 z1;
    v2 = poly12_mul x1 z2
  in
    if v1 = v2 then
      if u1 = u2 then fq12_point_double (x1, y1, z1)
      else (poly12_one, poly12_one, poly12_zero)
    else let
      u = poly12_sub u1 u2;
      v = poly12_sub v1 v2;
      v_sq = poly12_sqr v;
      v_sq_v2 = poly12_mul v_sq v2;
      v_cu = poly12_mul v v_sq;
      w = poly12_mul z1 z2;
      a = poly12_sub (poly12_sub (poly12_mul (poly12_sqr u) w) v_cu)
                     (poly12_scale 2 v_sq_v2);
      x3 = poly12_mul v a;
      y3 = poly12_sub (poly12_mul u (poly12_sub v_sq_v2 a)) (poly12_mul v_cu u2);
      z3 = poly12_mul v_cu w
    in (x3, y3, z3)
End

val () = cv_trans fq12_point_add_def;

(* Miller loop iteration *)
Definition miller_iter_def:
  miller_iter r q f_num f_den p n (i:num) =
  let
    (* Line function for doubling *)
    line_dbl = poly12_linefunc r r p;
    line_dbl_num = FST line_dbl;
    line_dbl_den = SND line_dbl;
    f_num = poly12_mul (poly12_sqr f_num) line_dbl_num;
    f_den = poly12_mul (poly12_sqr f_den) line_dbl_den;
    r = fq12_point_double r;
    (* Check if bit is set *)
    bit = (n DIV (2 ** i)) MOD 2;
    (r, f_num, f_den) =
      if bit = 1 then let
        line_add = poly12_linefunc r q p;
        line_add_num = FST line_add;
        line_add_den = SND line_add;
        f_num = poly12_mul f_num line_add_num;
        f_den = poly12_mul f_den line_add_den;
        r = fq12_point_add r q
      in (r, f_num, f_den)
      else (r, f_num, f_den)
  in if i = 0 then (r, f_num, f_den)
     else miller_iter r q f_num f_den p n (i - 1)
Termination
  WF_REL_TAC `measure (λ(_,_,_,_,_,_,i). i)`
End

val () = cv_trans miller_iter_def;

(* Main Miller loop *)
Definition miller_loop_def:
  miller_loop q_fq2 p =
  if g2_is_inf q_fq2 \/ g1_is_inf p then poly12_one
  else let
    cast_p = cast_g1_to_fq12 p;
    twist_q = twist q_fq2;
    result = miller_iter twist_q twist_q poly12_one poly12_one cast_p ate_loop_count 62;
    r = FST result;
    f_num = FST (SND result);
    f_den = SND (SND result);
    f = poly12_div f_num f_den
  in f
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

(* Hard part cofactor for final exponentiation *)
(* cofactor = (p^4 - p^2 + 1) / n *)
Definition final_exp_cofactor_def:
  final_exp_cofactor =
  3231341240655752096707584860803309478437141994360495287810090604918866498006918878659249295802437253802989038524276850003264865133760793251880240042428329968030428107361598743608900379391168613006314069481069143760609051456778663991635955024110850696193255199460910775773285930773384402756n
End

val () = cv_trans_deep_embedding EVAL final_exp_cofactor_def;

Definition final_exponentiation_def:
  final_exponentiation f =
  let
    f_easy = final_exp_easy f
  in poly12_exp f_easy final_exp_cofactor
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
  kzg_setup_g2 = ((2857478431788097897603529389378922220591357102918386496030560663056275599667894169125420065688265294287377632743855n,
                   1653399135728550144198379090078740512780949618986531514324998367956065906195430302376210864130737629055419125661284n),
                  (1654119979715276993429688632500930614598041036454780654537273960294116562964960369487968972960044621727716668581804n,
                   868085707067025444194664732861613854206876672028826058619065538880620529864003813757775033179228169648753220324104n),
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
