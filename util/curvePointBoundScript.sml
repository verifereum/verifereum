(*
 * The BN254 and BLS12-381 code computes curve points whose coordinates
 * stay below the field modulus, so their byte encodings have fixed
 * length.
 *
 * The affine conversions return a point's raw coordinates when z = 1, so
 * each operation (field arithmetic, add, double, scalar multiplication,
 * MSM, decoding, the isogeny maps) is shown to keep them reduced.
 *)
Theory curvePointBound
Ancestors
  arithmetic list rich_list numposrep logroot bitstring
  vfmTypes recursiveLengthPrefix bn254 bls12381
Libs
  BasicProvers wordsLib

Theorem LENGTH_num_to_be_bytes_le:
  n < 256 ** k ⇒ LENGTH (num_to_be_bytes n) ≤ k
Proof
  rw[LENGTH_num_to_be_bytes] \\ gvs[LT_EXP_LOG]
QED

(* -------------------------------------------------------------------------
 * BN254: the coordinates of a computed point are below the modulus.
 * ------------------------------------------------------------------------- *)

Theorem bn254p_gt1:
  0 < bn254p ∧ 1 < bn254p
Proof
  rw[bn254p_def]
QED

Theorem bn254_field_lt:
  bn254$fmul x y < bn254p ∧ bn254$fadd x y < bn254p ∧
  bn254$fsub x y < bn254p
Proof
  rw[bn254Theory.fmul_def, bn254Theory.fadd_def, bn254Theory.fsub_def]
  \\ rw[bn254p_def]
QED

Theorem bn254_add_lt:
  FST (bn254$add p q) < bn254p ∧ FST (SND (bn254$add p q)) < bn254p
Proof
  PairCases_on `p` \\ PairCases_on `q`
  \\ simp[bn254Theory.add_def, bn254_field_lt]
QED

Theorem bn254_mul_loop_lt:
  ∀a p n.
    FST a < bn254p ∧ FST (SND a) < bn254p ⇒
    FST (bn254$mul_loop a p n) < bn254p ∧
    FST (SND (bn254$mul_loop a p n)) < bn254p
Proof
  recInduct bn254Theory.mul_loop_ind \\ rpt gen_tac \\ strip_tac
  \\ strip_tac
  \\ once_rewrite_tac[bn254Theory.mul_loop_def]
  \\ IF_CASES_TAC \\ gvs[]
  \\ first_x_assum irule \\ rw[bn254_add_lt]
QED

Theorem bn254_mul_lt:
  FST p < bn254p ∧ FST (SND p) < bn254p ⇒
  FST (bn254$mul p n) < bn254p ∧ FST (SND (bn254$mul p n)) < bn254p
Proof
  strip_tac
  \\ rw[bn254Theory.mul_def, bn254Theory.zero_def, bn254p_gt1,
        bn254_mul_loop_lt]
QED

Theorem bn254_toAffine_lt:
  FST p < bn254p ∧ FST (SND p) < bn254p ⇒
  FST (toAffine p) < bn254p ∧ SND (toAffine p) < bn254p
Proof
  PairCases_on `p` \\ rw[toAffine_def, bn254_field_lt]
  \\ rw[bn254p_def]
QED

Theorem bn254_fromAffine_lt:
  validAffine a ⇒
  FST (fromAffine a) < bn254p ∧ FST (SND (fromAffine a)) < bn254p
Proof
  PairCases_on `a` \\ rw[validAffine_def, fromAffine_def, bn254Theory.zero_def]
  \\ rw[bn254p_def]
QED

Theorem LENGTH_bn254_coordinate:
  x < bn254p ⇒ LENGTH (PAD_LEFT 0w 32 (num_to_be_bytes x)) = 32
Proof
  strip_tac
  \\ `x < 256 ** 32` by (
       irule LESS_LESS_EQ_TRANS \\ qexists_tac `bn254p`
       \\ simp[] \\ EVAL_TAC)
  \\ drule LENGTH_num_to_be_bytes_le \\ rw[length_pad_left]
QED

(* -------------------------------------------------------------------------
 * BLS12-381: the coordinates of a decoded or computed point are below the
 * modulus.
 * ------------------------------------------------------------------------- *)

Theorem bls12381p_gt1:
  0 < bls12381p ∧ 1 < bls12381p
Proof
  rw[bls12381p_def]
QED

Theorem bls12381_field_lt:
  bls12381$fmul x y < bls12381p ∧ bls12381$fadd x y < bls12381p ∧
  bls12381$fsub x y < bls12381p ∧ bls12381$fneg x < bls12381p
Proof
  rw[bls12381Theory.fmul_def, bls12381Theory.fadd_def,
     bls12381Theory.fsub_def, bls12381Theory.fneg_def]
  \\ rw[bls12381p_def]
QED

Theorem bls12381_f2_lt:
  FST (bls12381$f2mul a b) < bls12381p ∧
  SND (bls12381$f2mul a b) < bls12381p ∧
  FST (bls12381$f2sqr a) < bls12381p ∧
  SND (bls12381$f2sqr a) < bls12381p ∧
  FST (bls12381$f2muls a k) < bls12381p ∧
  SND (bls12381$f2muls a k) < bls12381p ∧
  FST (bls12381$f2add a b) < bls12381p ∧
  SND (bls12381$f2add a b) < bls12381p ∧
  FST (bls12381$f2sub a b) < bls12381p ∧
  SND (bls12381$f2sub a b) < bls12381p
Proof
  PairCases_on `a` \\ PairCases_on `b`
  \\ simp[bls12381Theory.f2mul_def, bls12381Theory.f2sqr_def,
          bls12381Theory.f2muls_def, bls12381Theory.f2add_def,
          bls12381Theory.f2sub_def, bls12381_field_lt]
QED

Theorem LENGTH_encode_fq:
  n < bls12381p ⇒ LENGTH (encode_fq n) = 64
Proof
  strip_tac
  \\ `n < 256 ** 48` by (
       irule LESS_LESS_EQ_TRANS \\ qexists_tac `bls12381p`
       \\ simp[] \\ EVAL_TAC)
  \\ drule LENGTH_num_to_be_bytes_le \\ rw[encode_fq_def, length_pad_left]
QED

Theorem decode_fq_lt:
  decode_fq bs = SOME n ⇒ n < bls12381p
Proof
  rw[decode_fq_def]
QED

(* G1 *)

Theorem g1_double_lt:
  FST (g1_double p) < bls12381p ∧ FST (SND (g1_double p)) < bls12381p
Proof
  PairCases_on `p` \\ rw[g1_double_def, bls12381_field_lt, bls12381p_gt1]
QED

Theorem g1_add_lt:
  FST p < bls12381p ∧ FST (SND p) < bls12381p ∧
  FST q < bls12381p ∧ FST (SND q) < bls12381p ⇒
  FST (g1_add p q) < bls12381p ∧ FST (SND (g1_add p q)) < bls12381p
Proof
  PairCases_on `p` \\ PairCases_on `q`
  \\ rw[g1_add_def, bls12381_field_lt, bls12381p_gt1, g1_double_lt]
QED

Theorem g1_mul_loop_lt:
  ∀acc p n.
    FST acc < bls12381p ∧ FST (SND acc) < bls12381p ∧
    FST p < bls12381p ∧ FST (SND p) < bls12381p ⇒
    FST (g1_mul_loop acc p n) < bls12381p ∧
    FST (SND (g1_mul_loop acc p n)) < bls12381p
Proof
  recInduct g1_mul_loop_ind \\ rpt gen_tac \\ strip_tac \\ strip_tac
  \\ once_rewrite_tac[g1_mul_loop_def]
  \\ IF_CASES_TAC \\ gvs[]
  \\ first_x_assum irule \\ rw[g1_add_lt, g1_double_lt]
QED

Theorem g1_mul_lt:
  FST p < bls12381p ∧ FST (SND p) < bls12381p ⇒
  FST (g1_mul p n) < bls12381p ∧ FST (SND (g1_mul p n)) < bls12381p
Proof
  strip_tac \\ rw[g1_mul_def, g1_zero_def, bls12381p_gt1, g1_mul_loop_lt]
QED

Theorem g1_msm_lt:
  ∀ps. EVERY (λps. FST (FST ps) < bls12381p ∧
                   FST (SND (FST ps)) < bls12381p) ps ⇒
       FST (g1_msm ps) < bls12381p ∧ FST (SND (g1_msm ps)) < bls12381p
Proof
  recInduct g1_msm_ind
  \\ rw[g1_msm_def, g1_zero_def, bls12381p_gt1]
  \\ gvs[g1_add_lt, g1_mul_lt]
QED

Theorem decode_g1_lt:
  decode_g1 bs = SOME p ⇒ FST p < bls12381p ∧ FST (SND p) < bls12381p
Proof
  rw[decode_g1_def, AllCaseEqs()]
  \\ gvs[g1_zero_def, bls12381p_gt1]
  \\ imp_res_tac decode_fq_lt
QED

Theorem decode_g1_scalars_acc_lt:
  ∀acc bs ps.
    decode_g1_scalars_acc acc bs = SOME ps ∧
    EVERY (λps. FST (FST ps) < bls12381p ∧
                FST (SND (FST ps)) < bls12381p) acc ⇒
    EVERY (λps. FST (FST ps) < bls12381p ∧
                FST (SND (FST ps)) < bls12381p) ps
Proof
  recInduct decode_g1_scalars_acc_ind \\ rpt gen_tac \\ strip_tac
  \\ rpt gen_tac \\ strip_tac
  \\ qpat_x_assum `decode_g1_scalars_acc _ _ = _` mp_tac
  \\ once_rewrite_tac[decode_g1_scalars_acc_def]
  \\ rw[AllCaseEqs()] \\ gvs[EVERY_REVERSE]
  \\ first_x_assum irule \\ simp[]
  \\ gvs[decode_g1_scalar_def, AllCaseEqs()]
  \\ imp_res_tac decode_g1_lt \\ simp[]
QED

Theorem iso_map_g1_lt:
  FST (iso_map_g1 p) < bls12381p ∧ FST (SND (iso_map_g1 p)) < bls12381p
Proof
  PairCases_on `p` \\ simp[iso_map_g1_def, bls12381_field_lt]
QED

Theorem LENGTH_encode_g1:
  FST p < bls12381p ∧ FST (SND p) < bls12381p ⇒
  LENGTH (encode_g1 p) = 128
Proof
  PairCases_on `p` \\ rw[encode_g1_def, g1_to_affine_def, g1_is_inf_def]
  \\ simp[LENGTH_encode_fq, bls12381_field_lt]
QED

(* G2 *)

Theorem g2_double_lt:
  FST (FST (g2_double p)) < bls12381p ∧
  SND (FST (g2_double p)) < bls12381p ∧
  FST (FST (SND (g2_double p))) < bls12381p ∧
  SND (FST (SND (g2_double p))) < bls12381p
Proof
  PairCases_on `p`
  \\ rw[g2_double_def, g2_zero_def, f2one_def, bls12381_f2_lt,
        bls12381p_gt1]
QED

Theorem g2_add_lt:
  FST (FST p) < bls12381p ∧ SND (FST p) < bls12381p ∧
  FST (FST (SND p)) < bls12381p ∧ SND (FST (SND p)) < bls12381p ∧
  FST (FST q) < bls12381p ∧ SND (FST q) < bls12381p ∧
  FST (FST (SND q)) < bls12381p ∧ SND (FST (SND q)) < bls12381p ⇒
  FST (FST (g2_add p q)) < bls12381p ∧
  SND (FST (g2_add p q)) < bls12381p ∧
  FST (FST (SND (g2_add p q))) < bls12381p ∧
  SND (FST (SND (g2_add p q))) < bls12381p
Proof
  PairCases_on `p` \\ PairCases_on `q`
  \\ rw[g2_add_def, g2_zero_def, f2one_def, bls12381_f2_lt,
        bls12381p_gt1, g2_double_lt]
QED

Theorem g2_mul_loop_lt:
  ∀acc p n.
    FST (FST acc) < bls12381p ∧ SND (FST acc) < bls12381p ∧
    FST (FST (SND acc)) < bls12381p ∧ SND (FST (SND acc)) < bls12381p ∧
    FST (FST p) < bls12381p ∧ SND (FST p) < bls12381p ∧
    FST (FST (SND p)) < bls12381p ∧ SND (FST (SND p)) < bls12381p ⇒
    FST (FST (g2_mul_loop acc p n)) < bls12381p ∧
    SND (FST (g2_mul_loop acc p n)) < bls12381p ∧
    FST (FST (SND (g2_mul_loop acc p n))) < bls12381p ∧
    SND (FST (SND (g2_mul_loop acc p n))) < bls12381p
Proof
  recInduct g2_mul_loop_ind \\ rpt gen_tac \\ strip_tac \\ strip_tac
  \\ once_rewrite_tac[g2_mul_loop_def]
  \\ IF_CASES_TAC \\ gvs[]
  \\ first_x_assum irule \\ rw[g2_add_lt, g2_double_lt]
QED

Theorem g2_zero_lt:
  FST (FST g2_zero) < bls12381p ∧ SND (FST g2_zero) < bls12381p ∧
  FST (FST (SND g2_zero)) < bls12381p ∧ SND (FST (SND g2_zero)) < bls12381p
Proof
  rw[g2_zero_def, f2one_def, bls12381p_gt1]
QED

Theorem g2_mul_lt:
  FST (FST p) < bls12381p ∧ SND (FST p) < bls12381p ∧
  FST (FST (SND p)) < bls12381p ∧ SND (FST (SND p)) < bls12381p ⇒
  FST (FST (g2_mul p n)) < bls12381p ∧
  SND (FST (g2_mul p n)) < bls12381p ∧
  FST (FST (SND (g2_mul p n))) < bls12381p ∧
  SND (FST (SND (g2_mul p n))) < bls12381p
Proof
  strip_tac \\ rw[g2_mul_def, g2_zero_lt, g2_mul_loop_lt]
QED

Theorem g2_msm_lt:
  ∀ps. EVERY (λps. FST (FST (FST ps)) < bls12381p ∧
                   SND (FST (FST ps)) < bls12381p ∧
                   FST (FST (SND (FST ps))) < bls12381p ∧
                   SND (FST (SND (FST ps))) < bls12381p) ps ⇒
       FST (FST (g2_msm ps)) < bls12381p ∧
       SND (FST (g2_msm ps)) < bls12381p ∧
       FST (FST (SND (g2_msm ps))) < bls12381p ∧
       SND (FST (SND (g2_msm ps))) < bls12381p
Proof
  recInduct g2_msm_ind
  \\ rw[g2_msm_def, g2_zero_lt]
  \\ gvs[g2_add_lt, g2_mul_lt]
QED

Theorem decode_fq2_lt:
  decode_fq2 bs = SOME x ⇒ FST x < bls12381p ∧ SND x < bls12381p
Proof
  rw[decode_fq2_def, AllCaseEqs()] \\ imp_res_tac decode_fq_lt \\ simp[]
QED

Theorem decode_g2_lt:
  decode_g2 bs = SOME p ⇒
  FST (FST p) < bls12381p ∧ SND (FST p) < bls12381p ∧
  FST (FST (SND p)) < bls12381p ∧ SND (FST (SND p)) < bls12381p
Proof
  rw[decode_g2_def, AllCaseEqs()]
  \\ gvs[g2_zero_lt]
  \\ imp_res_tac decode_fq2_lt \\ simp[]
QED

Theorem decode_g2_scalars_acc_lt:
  ∀acc bs ps.
    decode_g2_scalars_acc acc bs = SOME ps ∧
    EVERY (λps. FST (FST (FST ps)) < bls12381p ∧
                SND (FST (FST ps)) < bls12381p ∧
                FST (FST (SND (FST ps))) < bls12381p ∧
                SND (FST (SND (FST ps))) < bls12381p) acc ⇒
    EVERY (λps. FST (FST (FST ps)) < bls12381p ∧
                SND (FST (FST ps)) < bls12381p ∧
                FST (FST (SND (FST ps))) < bls12381p ∧
                SND (FST (SND (FST ps))) < bls12381p) ps
Proof
  recInduct decode_g2_scalars_acc_ind \\ rpt gen_tac \\ strip_tac
  \\ rpt gen_tac \\ strip_tac
  \\ qpat_x_assum `decode_g2_scalars_acc _ _ = _` mp_tac
  \\ once_rewrite_tac[decode_g2_scalars_acc_def]
  \\ rw[AllCaseEqs()] \\ gvs[EVERY_REVERSE]
  \\ first_x_assum irule \\ simp[]
  \\ gvs[decode_g2_scalar_def, AllCaseEqs()]
  \\ imp_res_tac decode_g2_lt \\ simp[]
QED

Theorem iso_map_g2_lt:
  FST (FST (iso_map_g2 p)) < bls12381p ∧
  SND (FST (iso_map_g2 p)) < bls12381p ∧
  FST (FST (SND (iso_map_g2 p))) < bls12381p ∧
  SND (FST (SND (iso_map_g2 p))) < bls12381p
Proof
  PairCases_on `p` \\ simp[iso_map_g2_def, bls12381_f2_lt]
QED

Theorem LENGTH_encode_fq2:
  FST x < bls12381p ∧ SND x < bls12381p ⇒ LENGTH (encode_fq2 x) = 128
Proof
  PairCases_on `x` \\ rw[encode_fq2_def, LENGTH_encode_fq]
QED

Theorem bls12381_f2inv_lt:
  FST (f2inv a) < bls12381p ∧ SND (f2inv a) < bls12381p
Proof
  PairCases_on `a` \\ simp[f2inv_def, bls12381_field_lt]
QED

Theorem LENGTH_encode_g2:
  FST (FST p) < bls12381p ∧ SND (FST p) < bls12381p ∧
  FST (FST (SND p)) < bls12381p ∧ SND (FST (SND p)) < bls12381p ⇒
  LENGTH (encode_g2 p) = 256
Proof
  PairCases_on `p`
  \\ rw[encode_g2_def, g2_to_affine_def, g2_is_inf_def]
  \\ simp[LENGTH_encode_fq2, bls12381_f2_lt]
QED

(* The BLS12-381 precompiles' outputs. *)

Theorem LENGTH_bls_outputs:
  (bls_g1add input = SOME r ⇒ LENGTH r = 128) ∧
  (bls_g1msm input = SOME r ⇒ LENGTH r = 128) ∧
  (bls_g2add input = SOME r ⇒ LENGTH r = 256) ∧
  (bls_g2msm input = SOME r ⇒ LENGTH r = 256) ∧
  (bls_pairing input = SOME r ⇒ LENGTH r = 32) ∧
  (bls_map_fp_to_g1 input = SOME r ⇒ LENGTH r = 128) ∧
  (bls_map_fp2_to_g2 input = SOME r ⇒ LENGTH r = 256)
Proof
  rpt conj_tac \\ strip_tac
  >- (gvs[bls_g1add_def, AllCaseEqs()]
      \\ imp_res_tac decode_g1_lt
      \\ irule LENGTH_encode_g1 \\ simp[g1_add_lt])
  >- (gvs[bls_g1msm_def, AllCaseEqs(), decode_g1_scalars_def]
      \\ drule decode_g1_scalars_acc_lt \\ simp[] \\ strip_tac
      \\ irule LENGTH_encode_g1 \\ simp[g1_msm_lt])
  >- (gvs[bls_g2add_def, AllCaseEqs()]
      \\ imp_res_tac decode_g2_lt
      \\ irule LENGTH_encode_g2 \\ simp[g2_add_lt])
  >- (gvs[bls_g2msm_def, AllCaseEqs(), decode_g2_scalars_def]
      \\ drule decode_g2_scalars_acc_lt \\ simp[] \\ strip_tac
      \\ irule LENGTH_encode_g2 \\ simp[g2_msm_lt])
  >- gvs[bls_pairing_def, AllCaseEqs()]
  >- (gvs[bls_map_fp_to_g1_def, AllCaseEqs()]
      \\ irule LENGTH_encode_g1 \\ simp[g1_mul_lt, iso_map_g1_lt])
  \\ gvs[bls_map_fp2_to_g2_def, AllCaseEqs()]
  \\ irule LENGTH_encode_g2 \\ simp[g2_mul_lt, iso_map_g2_lt]
QED
