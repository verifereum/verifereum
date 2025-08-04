open HolKernel boolLib bossLib Parse wordsLib cv_transLib
     cv_stdTheory listTheory wordsTheory byteTheory vfmTypesTheory

val () = new_theory "blake2f";

(*
Definition iv_def:
  iv: word64 list = [
     0x6A09E667F3BCC908w; 0xBB67AE8584CAA73Bw;
     0x3C6EF372FE94F82Bw; 0xA54FF53A5F1D36F1w;
     0x510E527FADE682D1w; 0x9B05688C2B3E6C1Fw;
     0x1F83D9ABFB41BD6Bw; 0x5BE0CD19137E2179w]
End

EVAL“0x1F83D9ABFB41BD6Bw ??
    (0xFFFFFFFFFFFFFFFFw:word64)”
*)

Definition rotr_def:
  rotr n (x: word64) = x >>> n ?? x << (64 - n)
End

val () = cv_auto_trans rotr_def;

Definition blake2g_def:
  blake2g va vb vc vd x (y:word64) = let
    va = va + vb + x;
    vd = rotr 32 (vd ⊕ va);
    vc = vc + vd;
    vb = rotr 24 (vb ⊕ vc);
    va = va + vb + y;
    vd = rotr 16 (vd ⊕ va);
    vc = vc + vd;
    vb = rotr 63 (vb ⊕ vc)
  in (va, vb, vc, vd)
End

val () = cv_auto_trans blake2g_def;

Definition sigmas_def:
  sigmas : num list list =
  [[ 0;  1;  2;  3;  4;  5;  6;  7;  8;  9; 10; 11; 12; 13; 14; 15];
   [14; 10;  4;  8;  9; 15; 13;  6;  1; 12;  0;  2; 11;  7;  5;  3];
   [11;  8; 12;  0;  5;  2; 15; 13; 10; 14;  3;  6;  7;  1;  9;  4];
   [ 7;  9;  3;  1; 13; 12; 11; 14;  2;  6;  5; 10;  4;  0; 15;  8];
   [ 9;  0;  5;  7;  2;  4; 10; 15; 14;  1; 11; 12;  6;  8;  3; 13];
   [ 2; 12;  6; 10;  0; 11;  8;  3;  4; 13;  7;  5; 15; 14;  1;  9];
   [12;  5;  1; 15; 14; 13;  4; 10;  0;  7;  6;  3;  9;  2;  8; 11];
   [13; 11;  7; 14; 12;  1;  3;  9;  5;  0; 15;  4;  8;  6;  2; 10];
   [ 6; 15; 14;  9; 11;  3;  0;  8; 12;  2; 13;  7;  1;  4; 10;  5];
   [10;  2;  8;  4;  7;  6;  1;  5; 15; 11;  9; 14;  3; 12; 13;  0]]
End

val () = cv_trans_deep_embedding EVAL sigmas_def;

Definition body_def:
  body v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 m s = let
    i = HD s; s = TL s; j = HD s; s = TL s;
    (v0, v4, v8, v12) = blake2g v0 v4 v8 v12 (EL i m) (EL j m);
    i = HD s; s = TL s; j = HD s; s = TL s;
    (v1, v5, v9, v13) = blake2g v1 v5 v9 v13 (EL i m) (EL j m);
    i = HD s; s = TL s; j = HD s; s = TL s;
    (v2, v6, v10, v14) = blake2g v2 v6 v10 v14 (EL i m) (EL j m);
    i = HD s; s = TL s; j = HD s; s = TL s;
    (v3, v7, v11, v15) = blake2g v3 v7 v11 v15 (EL i m) (EL j m);
    i = HD s; s = TL s; j = HD s; s = TL s;
    (v0, v5, v10, v15) = blake2g v0 v5 v10 v15 (EL i m) (EL j m);
    i = HD s; s = TL s; j = HD s; s = TL s;
    (v1, v6, v11, v12) = blake2g v1 v6 v11 v12 (EL i m) (EL j m);
    i = HD s; s = TL s; j = HD s; s = TL s;
    (v2, v7, v8, v13) = blake2g v2 v7 v8 v13 (EL i m) (EL j m);
    i = HD s; s = TL s; j = HD s;
    (v3, v4, v9, v14) = blake2g v3 v4 v9 v14 (EL i m) (EL j m)
  in
    (v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15)
End

val body_pre_def = cv_trans_pre "body_pre" body_def;

Theorem body_pre_length:
  EVERY (λi. i < LENGTH m) s ∧ LENGTH s = 16 ⇒
  body_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m s
Proof
  rw[body_pre_def]
  \\ gvs[LENGTH_EQ_NUM_compute]
QED

Definition loop_def:
  loop v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 m ss 0 =
    (v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15) ∧
  loop v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 m ss (SUC n) =
  let (s, ss) = case ss of s::ss => (s, ss) | [] => (HD sigmas, TL sigmas) in
  let (v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15)
   = body v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 m s
  in loop v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 m ss n
End

val loop_pre_def = cv_trans_pre "loop_pre" loop_def;

Theorem loop_pre_length:
  EVERY (λs. LENGTH s = 16 ∧ EVERY (λi. i < LENGTH m) s) (sigmas ++ ss)
  ⇒ loop_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m ss n
Proof
  (fn g as (_,w) => map_every ID_SPEC_TAC (free_vars w) g)
  \\ Induct_on`n`
  \\ rw[Once loop_pre_def]
  >- rw[sigmas_def]
  >- (
    irule body_pre_length
    \\ gvs[CaseEq"list"]
    \\ Cases_on`sigmas` >- fs[sigmas_def]
    \\ gvs[] )
  \\ gvs[CaseEq"list"]
  \\ first_x_assum irule
  \\ Cases_on`sigmas` >- fs[sigmas_def]
  \\ gvs[]
QED

Definition blake2f_def:
  blake2f r hs m t0 t1 (flag: word8) = let
    h0 = HD hs; hs = TL hs;
    h1 = HD hs; hs = TL hs;
    h2 = HD hs; hs = TL hs;
    h3 = HD hs; hs = TL hs;
    h4 = HD hs; hs = TL hs;
    h5 = HD hs; hs = TL hs;
    h6 = HD hs; hs = TL hs;
    h7 = HD hs; hs = TL hs;
    v8 = 0x6A09E667F3BCC908w;
    v9 = 0xBB67AE8584CAA73Bw;
    v10 = 0x3C6EF372FE94F82Bw;
    v11 = 0xA54FF53A5F1D36F1w;
    v12 = 0x510E527FADE682D1w ⊕ t0;
    v13 = 0x9B05688C2B3E6C1Fw ⊕ t1;
    v14 = if flag = 1w then 0xE07C265404BE4294w else 0x1F83D9ABFB41BD6Bw;
    v15 = 0x5BE0CD19137E2179w;
    (v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15)
    = loop h0 h1 h2 h3 h4 h5 h6 h7 v8 v9 v10 v11 v12 v13 v14 v15 m [] r;
    h0 = word_to_bytes (h0 ?? v0 ?? v8) F;
    h1 = word_to_bytes (h1 ?? v1 ?? v9) F;
    h2 = word_to_bytes (h2 ?? v2 ?? v10) F;
    h3 = word_to_bytes (h3 ?? v3 ?? v11) F;
    h4 = word_to_bytes (h4 ?? v4 ?? v12) F;
    h5 = word_to_bytes (h5 ?? v5 ?? v13) F;
    h6 = word_to_bytes (h6 ?? v6 ?? v14) F;
    h7 = word_to_bytes (h7 ?? v7 ?? v15) F;
  in FLAT [h0;h1;h2;h3;h4;h5;h6;h7]
End

val blake2f_pre_def = cv_trans_pre "blake2f_pre" blake2f_def;

Theorem blake2f_pre_length:
  LENGTH hs = 8 ∧ LENGTH m = 16 ⇒
  blake2f_pre _ hs m _ _ _
Proof
  rw[blake2f_pre_def]
  \\ gvs[LENGTH_EQ_NUM_compute]
  \\ irule loop_pre_length
  \\ rw[sigmas_def]
QED

val () = export_theory ();
