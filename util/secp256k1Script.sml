open HolKernel boolLib bossLib Parse wordsLib
     arithmeticTheory
     vfmTypesTheory cv_stdTheory cv_transLib

val () = new_theory "secp256k1";

(* TODO: move *)

val findq_pre_def = cv_trans_pre findq_thm;

Theorem findq_pre[cv_pre]:
  findq_pre x
Proof
  completeInduct_on`FST(SND x) - SND(SND x)`
  \\ rw[Once findq_pre_def] \\ gvs[]
QED

val DIVMOD_pre_def = cv_trans_pre DIVMOD_THM;

Theorem DIVMOD_pre[cv_pre]:
  DIVMOD_pre x
Proof
  completeInduct_on`FST(SND x)`
  \\ rw[Once DIVMOD_pre_def]
  \\ first_x_assum irule \\ rw[]
  \\ CCONTR_TAC \\ gvs[findq_eq_0]
QED

(* -- *)

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
  fmul x y = (x * y) MOD secp256k1P
End

val () = cv_trans fmul_def;

Definition fadd_def:
  fadd x y = (x + y) MOD secp256k1P
End

val () = cv_trans fadd_def;

Definition fsub_def:
  fsub x y = if x < y then x + secp256k1P - y
             else (x - y) MOD secp256k1P
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

Definition nmul_def:
  nmul x y = (x * y) MOD secp256k1N
End

val () = cv_trans nmul_def;

Definition nsub_def:
  nsub x y = if x < y then x + secp256k1N - y
             else (x - y) MOD secp256k1N
End

val () = cv_trans nsub_def;

Definition endo_def:
  endo k = let
  c1 = divNearest (endob2 * k) secp256k1N;
  c2 = divNearest (endonegb1 * k) secp256k1N;
  k1 = nsub (nsub k (nmul c1 endoa1)) (nmul c2 endoa2);
  k2 = nsub (nmul endonegb1 c1) (nmul endob2 c2);
  k1neg = (k1 > pow2_128);
  k2neg = (k2 > pow2_128);
  k1 = if k1neg then secp256k1N - k1 else k1;
  k2 = if k2neg then secp256k1N - k2 else k2
  in (k1, k1neg, k2, k2neg)
End

val () = cv_trans endo_def;

Definition endobeta_def:
  endobeta = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501een
End

val () = cv_trans_deep_embedding EVAL endobeta_def;

Definition fneg_def:
  fneg x = secp256k1P - x
End

val () = cv_trans fneg_def;

Definition neg_def:
  neg (x:num,y,z:num) = (x, fneg y, z)
End

val () = cv_trans neg_def;

Definition mul_loop_def:
  mul_loop k1p k2p k1 k2 d =
  if k1 = 0 ∧ k2 = 0 then (k1p, k2p)
  else let
    k1p = if ODD k1 then add k1p d else k1p;
    k2p = if ODD k2 then add k2p d else k2p;
    d = dbl d;
    k1 = k1 DIV 2;
    k2 = k2 DIV 2
  in mul_loop k1p k2p k1 k2 d
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λ(_,_,k1,k2,_). (k1, k2))’
  \\ rw[]
  \\ Cases_on`k1 = 0` \\ gvs[]
End

val () = cv_trans mul_loop_def;

Definition mul_def:
  mul p n =
  if n = 0 then zero else
  if p = zero ∨ n = 1 then p else
  let (k1, k1neg, k2, k2neg) = endo n in
  let (k1p, k2p) = mul_loop zero zero k1 k2 p in
  let k1p = if k1neg then neg k1p else k1p in
  let k2p = if k2neg then neg k2p else k2p in
  let k2p = (fmul (FST k2p) endobeta, FST(SND k2p), SND(SND k2p)) in
  add k1p k2p
End

val () = cv_trans mul_def;

Definition finv_loop_def:
  finv_loop a b x y u v =
  if a = 0 then x else let
    (q,r) = DIVMOD (0, b, a);
    m = fsub x (fmul u q);
    n = fsub y (fmul v q);
    b = a; a = r; x = u; y = v; u = m; v = n in
      finv_loop a b x y u v
Termination
  WF_REL_TAC ‘measure FST’
  \\ rw[]
  \\ pop_assum mp_tac
  \\ rw[DIVMOD_CORRECT]
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
  finv n = finv_loop n secp256k1P 0 1 1 0
End

val () = cv_trans finv_def;

Definition finvN_loop_def:
  finvN_loop a b x y u v =
  if a = 0 then x else let
    (q,r) = DIVMOD (0, b, a);
    m = nsub x (nmul u q);
    n = nsub y (nmul v q);
    b = a; a = r; x = u; y = v; u = m; v = n in
      finvN_loop a b x y u v
Termination
  WF_REL_TAC ‘measure FST’
  \\ rw[]
  \\ pop_assum mp_tac
  \\ rw[DIVMOD_CORRECT]
End

val finvN_loop_pre_def = cv_trans_pre finvN_loop_def;

Theorem finvN_loop_pre[cv_pre]:
  ∀a b x y u v. finvN_loop_pre a b x y u v
Proof
  ho_match_mp_tac finvN_loop_ind
  \\ rw[]
  \\ rw[Once finvN_loop_pre_def]
  \\ gvs[]
QED

Definition finvN_def:
  finvN n = finvN_loop n secp256k1N 0 1 1 0
End

val () = cv_trans finvN_def;

Definition weierstrassEquation_def:
  weierstrassEquation x = let
    x2 = fmul x x;
    x3 = fmul x2 x;
    xa = fmul x secp256k1a
  in fadd (fadd x3 xa) secp256k1b
End

val () = cv_trans weierstrassEquation_def;

Definition fpow_loop_def:
  fpow_loop p d power =
  if power = 0 then p else let
    p = if ODD power then fmul p d else p;
    d = fmul d d;
    power = power DIV 2
  in fpow_loop p d power
End

val () = cv_trans fpow_loop_def;

Definition fpow_def:
  fpow n p =
  if p = 0 then 1 else
  if p = 1 then n else
  fpow_loop 1 n p
End

val () = cv_trans fpow_def;

Definition p1mod2_def:
  p1mod2 = (secp256k1P - 1) DIV 2
End

val () = cv_trans_deep_embedding EVAL p1mod2_def;

Definition fleg_def:
  fleg n = fpow n p1mod2
End

val () = cv_trans fleg_def;

Definition sqrtS_def:
  sqrtS = 6n
End

val () = cv_trans_deep_embedding EVAL sqrtS_def;

Definition sqrtQ_def:
  sqrtQ =  p1mod2 ** sqrtS
End

val () = cv_trans_deep_embedding EVAL sqrtQ_def;

Definition Q1div2_def:
  Q1div2 = (sqrtQ + 1) DIV 2
End

val () = cv_trans_deep_embedding EVAL Q1div2_def;

Definition sqrtZ_def:
  sqrtZ = 5n
End

val () = cv_trans_deep_embedding EVAL sqrtZ_def;

Definition sqrtcc_def:
  sqrtcc = fpow sqrtZ sqrtQ
End

val () = cv_trans_deep_embedding cv_eval sqrtcc_def;

Definition fsqrt_inner_loop_def:
  fsqrt_inner_loop M t i =
  if i ≥ M then M else
  if t = 1 then i else
    fsqrt_inner_loop M (fmul t t) (SUC i)
Termination
  WF_REL_TAC ‘measure (λ(m,t,i). m - i)’
End

val () = cv_trans fsqrt_inner_loop_def;

Definition fsqrt_loop_def:
  fsqrt_loop M c t R =
  if t = 1 then R else
  if t = 0 then 0 else let
  i = fsqrt_inner_loop M (fmul t t) 1;
  exponent = 2 ** (M - i - 1);
  b = fpow c exponent;
  c = fmul b b;
  t = fmul t c;
  R = fmul R b
  in if i ≥ M then 0 else fsqrt_loop i c t R
Termination
  WF_REL_TAC ‘measure FST’
End

val () = cv_trans fsqrt_loop_def;

Definition fsqrt_def:
  fsqrt n =
  if n = 0 then n else let
  M = sqrtS;
  t = fpow n sqrtQ;
  R = fpow n Q1div2 in
    fsqrt_loop M sqrtcc t R
End

val () = cv_trans fsqrt_def;

Definition recoverPoint_def:
  recoverPoint r s yParity (msgHash: bytes32) = let
    y2 = weierstrassEquation r;
    y = fsqrt y2;
    y = if ODD yParity = ODD y then y else fneg y;
    R = (r, y, 1n);
    ir = finvN r;
    h = (w2n msgHash) MOD secp256k1N;
    u1 = ((secp256k1N - h) * ir) MOD secp256k1N;
    u2 = (s * ir) MOD secp256k1N;
  in add (mul base u1) (mul R u2)
End

val () = cv_trans recoverPoint_def;

Definition pointToUncompressedBytes_def:
 pointToUncompressedBytes (x,y,z) =
 let (ax, ay) =
   if z = 1 then (x, y) else
   let iz = finv z in
     (fmul x iz, fmul y iz) in
 (PAD_LEFT 0w 32 $ num_to_be_bytes ax) ++
 (PAD_LEFT 0w 32 $ num_to_be_bytes ay)
End

val () = cv_trans pointToUncompressedBytes_def;

val () = export_theory();
