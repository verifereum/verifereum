(*
 * Every frame's return data is shorter than 2 ** 256 bytes.
 *
 * A step sets a frame's return data in one of four ways: RETURN or REVERT
 * read it from memory, at most as many bytes as their size operand, a
 * stack word; a precompile writes its output; a finished call hands the
 * callee's return data to the caller; and most other steps that touch it
 * clear it. A precompile's output is either of fixed size or, for the
 * identity precompile, its input, which is its frame's call data. So the
 * invariant carried through each operation of a step bounds both the
 * return data and the call data of every frame.
 *
 * The BLS12-381 and BN254 precompiles encode curve points whose
 * coordinates are field elements. Their encodings have fixed length only
 * because those coordinates stay below the field modulus, which the
 * first part of this theory proves.
 *)
Theory vfmReturndataBound
Ancestors
  arithmetic list rich_list pair words numposrep logroot bitstring
  vfmTypes vfmBuffer vfmContext vfmExecution vfmExecutionProp
  vfmCalldataBound recursiveLengthPrefix blake2f bn254 bls12381
Libs
  BasicProvers wordsLib

Definition returndata_bounded_def:
  returndata_bounded s ⇔
    EVERY (λc. LENGTH c.returnData < 2 ** 256) (MAP FST s.contexts)
End

(* -------------------------------------------------------------------------
 * Lengths of encoded numbers.
 * ------------------------------------------------------------------------- *)

Theorem LENGTH_num_to_be_bytes_le:
  n < 256 ** k ⇒ LENGTH (num_to_be_bytes n) ≤ k
Proof
  rw[LENGTH_num_to_be_bytes] \\ gvs[LT_EXP_LOG]
QED

Theorem LENGTH_n2l_256_le:
  n < 256 ** k ∧ 0 < k ⇒ LENGTH (n2l 256 n) ≤ k
Proof
  rw[LENGTH_n2l] \\ gvs[LT_EXP_LOG]
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

Theorem ecadd_lt:
  ecadd a b = SOME (x, y) ⇒ x < bn254p ∧ y < bn254p
Proof
  rw[ecadd_def, addAffine_def]
  \\ qspec_then `bn254$add (fromAffine a) (fromAffine b)` mp_tac
       (GEN_ALL bn254_toAffine_lt)
  \\ simp[bn254_add_lt]
QED

Theorem ecmul_lt:
  ecmul a n = SOME (x, y) ⇒ x < bn254p ∧ y < bn254p
Proof
  rw[ecmul_def, mulAffine_def]
  \\ qspec_then `bn254$mul (fromAffine a) n` mp_tac (GEN_ALL bn254_toAffine_lt)
  \\ simp[bn254_mul_lt, bn254_fromAffine_lt]
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

(* Other precompiles' outputs. *)

Theorem LENGTH_blake2f:
  LENGTH (blake2f r hs m t0 t1 flag) = 64
Proof
  rw[blake2f_def] \\ pairarg_tac \\ simp[dimindex_64]
QED

Theorem LENGTH_point_eval_output:
  LENGTH point_eval_output = 64
Proof
  EVAL_TAC
QED

Theorem LENGTH_modexp_output:
  LENGTH (n2l 256 (modexp b e (l2n 256 (REVERSE (MAP w2n (take_pad_0 z ls))))
                    1)) ≤ z ∨
  l2n 256 (REVERSE (MAP w2n (take_pad_0 z ls))) = 0
Proof
  qmatch_goalsub_abbrev_tac `modexp b e m 1`
  \\ Cases_on `m = 0` \\ simp[]
  \\ `m < 256 ** z` by (
       qspecl_then [`REVERSE (MAP w2n (take_pad_0 z ls))`, `256`]
         mp_tac l2n_lt
       \\ simp[Abbr`m`])
  \\ `0 < z` by (CCONTR_TAC \\ gvs[])
  \\ irule LENGTH_n2l_256_le \\ simp[modexp_exp]
  \\ irule LESS_TRANS \\ qexists_tac `m` \\ simp[]
QED

(* -------------------------------------------------------------------------
 * The invariant through each operation of a step: every frame's return
 * data and call data are shorter than 2 ** 256 bytes.
 * ------------------------------------------------------------------------- *)

Definition bounded_context_def:
  bounded_context c ⇔
    LENGTH c.returnData < 2 ** 256 ∧
    buffer_length c.msgParams.data < 2 ** 256
End

Definition preserves_bounded_contexts_def:
  preserves_bounded_contexts (m: α execution) ⇔
    ∀s. EVERY bounded_context (MAP FST s.contexts) ⇒
        EVERY bounded_context (MAP FST (SND (m s)).contexts)
End

Theorem bounded_contexts_eq:
  EVERY bounded_context (MAP FST s.contexts) ⇔
  returndata_bounded s ∧ calldata_bounded s
Proof
  rw[returndata_bounded_def, calldata_bounded_def, bounded_context_def,
     EVERY_MEM]
  \\ metis_tac[]
QED

Theorem bounded_context_update:
  (bounded_context (c with stack updated_by f1) ⇔ bounded_context c) ∧
  (bounded_context (c with memory updated_by f2) ⇔ bounded_context c) ∧
  (bounded_context (c with pc updated_by f3) ⇔ bounded_context c) ∧
  (bounded_context (c with jumpDest updated_by f4) ⇔ bounded_context c) ∧
  (bounded_context (c with gasUsed updated_by f5) ⇔ bounded_context c) ∧
  (bounded_context (c with addRefund updated_by f6) ⇔ bounded_context c) ∧
  (bounded_context (c with subRefund updated_by f7) ⇔ bounded_context c) ∧
  (bounded_context (c with logs updated_by f8) ⇔ bounded_context c)
Proof
  rw[bounded_context_def]
QED

Theorem bounded_context_lengths:
  bounded_context c ⇒
  LENGTH c.returnData < 2 ** 256 ∧
  LENGTH (buffer_to_list c.msgParams.data) < 2 ** 256
Proof
  rw[bounded_context_def]
QED

Theorem bounded_initial_context:
  LENGTH t.data < 2 ** 256 ⇒
  bounded_context (initial_context callee code static rd t)
Proof
  rw[bounded_context_def, initial_context_def, initial_msg_params_def]
QED

Theorem w2n_bytes32_lt:
  w2n (w: bytes32) < 2 ** 256
Proof
  assume_tac (INST_TYPE [alpha |-> ``:256``] w2n_lt) \\ gvs[dimword_def]
QED

Theorem LENGTH_buffer_take_lt:
  sz < n ⇒ LENGTH (buffer_take off sz b) < n
Proof
  rw[buffer_take_to_list, LENGTH_TAKE_EQ]
QED

(* Composition. *)

Theorem preserves_bounded_contexts_bind:
  preserves_bounded_contexts g ∧
  (∀x. preserves_bounded_contexts (f x)) ⇒
  preserves_bounded_contexts (bind g f)
Proof
  rw[preserves_bounded_contexts_def, bind_def]
  \\ CASE_TAC \\ gs[]
  \\ CASE_TAC \\ gs[]
  \\ metis_tac[SND]
QED

Theorem preserves_bounded_contexts_ignore_bind:
  preserves_bounded_contexts g ∧ preserves_bounded_contexts f ⇒
  preserves_bounded_contexts (ignore_bind g f)
Proof
  rw[ignore_bind_def] \\ irule preserves_bounded_contexts_bind \\ rw[]
QED

Theorem preserves_bounded_contexts_assert_bind:
  (b ⇒ preserves_bounded_contexts f) ⇒
  preserves_bounded_contexts (ignore_bind (assert b e) f)
Proof
  rw[preserves_bounded_contexts_def, ignore_bind_def, bind_def,
     assert_def]
QED

Theorem preserves_bounded_contexts_get_current_context_bind:
  (∀c. bounded_context c ⇒ preserves_bounded_contexts (f c)) ⇒
  preserves_bounded_contexts (bind get_current_context f)
Proof
  rw[preserves_bounded_contexts_def, bind_def, get_current_context_def,
     return_def, fail_def]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ first_x_assum irule \\ simp[]
QED

Theorem preserves_bounded_contexts_handle:
  preserves_bounded_contexts f ∧ (∀e. preserves_bounded_contexts (g e)) ⇒
  preserves_bounded_contexts (handle f g)
Proof
  rw[handle_def, preserves_bounded_contexts_def]
  \\ CASE_TAC \\ gs[]
  \\ CASE_TAC \\ gs[]
  \\ metis_tac[SND]
QED

(* Operations that do not change the frames. *)

Theorem preserves_bounded_contexts_same:
  (∀s. (SND (m s)).contexts = s.contexts) ⇒ preserves_bounded_contexts m
Proof
  rw[preserves_bounded_contexts_def]
QED

Theorem preserves_bounded_contexts_domain_check:
  preserves_bounded_contexts cont ⇒
  preserves_bounded_contexts (domain_check err check ad cont)
Proof
  rw[preserves_bounded_contexts_def, domain_check_def]
  \\ CASE_TAC
  \\ rw[ignore_bind_def, bind_def, set_domain_def, return_def, fail_def]
QED

Theorem preserves_bounded_contexts_basic[simp]:
  preserves_bounded_contexts (return x) ∧
  preserves_bounded_contexts (fail e) ∧
  preserves_bounded_contexts (assert b e) ∧
  preserves_bounded_contexts finish ∧
  preserves_bounded_contexts revert ∧
  preserves_bounded_contexts (reraise eo) ∧
  preserves_bounded_contexts get_num_contexts ∧
  preserves_bounded_contexts get_tx_params ∧
  preserves_bounded_contexts get_accounts ∧
  preserves_bounded_contexts (update_accounts f) ∧
  preserves_bounded_contexts get_tStorage ∧
  preserves_bounded_contexts (set_tStorage t) ∧
  preserves_bounded_contexts get_rollback ∧
  preserves_bounded_contexts (set_rollback r) ∧
  preserves_bounded_contexts get_original ∧
  preserves_bounded_contexts (set_original accs) ∧
  preserves_bounded_contexts (add_to_delete a) ∧
  preserves_bounded_contexts (set_domain d)
Proof
  rpt conj_tac \\ irule preserves_bounded_contexts_same
  \\ rw[return_def, fail_def, assert_def, finish_def, revert_def,
        reraise_def, get_num_contexts_def, get_tx_params_def,
        get_accounts_def, update_accounts_def, get_tStorage_def,
        set_tStorage_def, get_rollback_def, set_rollback_def,
        get_original_def, set_original_def, add_to_delete_def,
        set_domain_def]
QED

Theorem preserves_bounded_contexts_pop_context[simp]:
  preserves_bounded_contexts pop_context
Proof
  rw[preserves_bounded_contexts_def, pop_context_def, return_def, fail_def]
  \\ Cases_on `s.contexts` \\ gvs[]
QED

Theorem preserves_bounded_contexts_access[simp]:
  preserves_bounded_contexts (access_address a) ∧
  preserves_bounded_contexts (access_slot x) ∧
  preserves_bounded_contexts (ensure_storage_in_domain a)
Proof
  rw[access_address_def, access_slot_def, ensure_storage_in_domain_def]
  \\ irule preserves_bounded_contexts_domain_check
  \\ irule preserves_bounded_contexts_same \\ rw[return_def]
QED

(* Operations on the current frame. *)

Theorem preserves_bounded_contexts_set_current_context:
  bounded_context c ⇒ preserves_bounded_contexts (set_current_context c)
Proof
  rw[preserves_bounded_contexts_def, set_current_context_def, return_def,
     fail_def]
  \\ Cases_on `s.contexts` \\ gvs[]
QED

Theorem preserves_bounded_contexts_push_context:
  bounded_context (FST crb) ⇒ preserves_bounded_contexts (push_context crb)
Proof
  rw[preserves_bounded_contexts_def, push_context_def, return_def]
QED

val pres_simps = [preserves_bounded_contexts_set_current_context,
                  preserves_bounded_contexts_push_context,
                  bounded_context_update, bounded_context_lengths,
                  bounded_initial_context, w2n_bytes32_lt,
                  LENGTH_buffer_take_lt, UNCURRY];

val pres_tac =
  rpt (FIRST [irule preserves_bounded_contexts_get_current_context_bind,
              irule preserves_bounded_contexts_assert_bind,
              irule preserves_bounded_contexts_bind,
              irule preserves_bounded_contexts_ignore_bind,
              CASE_TAC, pairarg_tac] \\ rw pres_simps);

Theorem preserves_bounded_contexts_set_return_data:
  LENGTH rd < 2 ** 256 ⇒ preserves_bounded_contexts (set_return_data rd)
Proof
  strip_tac \\ rw[set_return_data_def] \\ pres_tac
  \\ irule preserves_bounded_contexts_set_current_context
  \\ gvs[bounded_context_def]
QED

val pres_simps =
  preserves_bounded_contexts_set_return_data :: pres_simps;

val pres_tac =
  rpt (FIRST [irule preserves_bounded_contexts_get_current_context_bind,
              irule preserves_bounded_contexts_assert_bind,
              irule preserves_bounded_contexts_bind,
              irule preserves_bounded_contexts_ignore_bind,
              CASE_TAC, pairarg_tac] \\ rw pres_simps);

Theorem preserves_bounded_contexts_frame_ops[simp]:
  preserves_bounded_contexts get_current_context ∧
  preserves_bounded_contexts get_gas_left ∧
  preserves_bounded_contexts get_callee ∧
  preserves_bounded_contexts get_caller ∧
  preserves_bounded_contexts get_value ∧
  preserves_bounded_contexts get_output_to ∧
  preserves_bounded_contexts get_return_data ∧
  preserves_bounded_contexts (get_return_data_check off sz) ∧
  preserves_bounded_contexts get_static ∧
  preserves_bounded_contexts (get_code a) ∧
  preserves_bounded_contexts get_current_code ∧
  preserves_bounded_contexts get_call_data ∧
  preserves_bounded_contexts (set_jump_dest j) ∧
  preserves_bounded_contexts (push_logs ls) ∧
  preserves_bounded_contexts (update_gas_refund ar) ∧
  preserves_bounded_contexts (consume_gas n) ∧
  preserves_bounded_contexts (unuse_gas n) ∧
  preserves_bounded_contexts (pop_stack n) ∧
  preserves_bounded_contexts (push_stack v) ∧
  preserves_bounded_contexts (memory_expansion_info off sz) ∧
  preserves_bounded_contexts (expand_memory n) ∧
  preserves_bounded_contexts (read_memory off sz) ∧
  preserves_bounded_contexts (write_memory off bs) ∧
  preserves_bounded_contexts inc_pc ∧
  preserves_bounded_contexts assert_not_static
Proof
  PairCases_on `ar`
  \\ rw[get_gas_left_def, get_callee_def, get_caller_def, get_value_def,
        get_output_to_def, get_return_data_def, get_return_data_check_def,
        get_static_def, get_code_def, get_current_code_def,
        get_call_data_def, set_jump_dest_def, push_logs_def,
        update_gas_refund_def, consume_gas_def, unuse_gas_def,
        pop_stack_def, push_stack_def, memory_expansion_info_def,
        expand_memory_def, read_memory_def, write_memory_def, inc_pc_def,
        assert_not_static_def]
  \\ TRY (irule preserves_bounded_contexts_same
          \\ rw[get_current_context_def, return_def, fail_def] \\ NO_TAC)
  \\ pres_tac
QED

Theorem preserves_bounded_contexts_copy_to_memory[simp]:
  (∀f. src = SOME f ⇒ preserves_bounded_contexts f) ⇒
  preserves_bounded_contexts (copy_to_memory gas off soff sz src) ∧
  preserves_bounded_contexts (step_copy_to_memory op src)
Proof
  strip_tac \\ rw[copy_to_memory_def, step_copy_to_memory_def] \\ pres_tac
QED

Theorem preserves_bounded_contexts_steps[simp]:
  preserves_bounded_contexts (step_binop op f) ∧
  preserves_bounded_contexts (step_monop op g) ∧
  preserves_bounded_contexts (step_modop op h) ∧
  preserves_bounded_contexts (step_context op i) ∧
  preserves_bounded_contexts (step_msgParams op j) ∧
  preserves_bounded_contexts (step_txParams op k) ∧
  preserves_bounded_contexts step_exp ∧
  preserves_bounded_contexts step_keccak256 ∧
  preserves_bounded_contexts (step_sload b) ∧
  preserves_bounded_contexts (step_sstore_gas_consumption a key v) ∧
  preserves_bounded_contexts (step_sstore b) ∧
  preserves_bounded_contexts step_balance ∧
  preserves_bounded_contexts step_call_data_load ∧
  preserves_bounded_contexts step_return_data_copy ∧
  preserves_bounded_contexts step_ext_code_size ∧
  preserves_bounded_contexts step_ext_code_copy ∧
  preserves_bounded_contexts step_ext_code_hash ∧
  preserves_bounded_contexts step_block_hash ∧
  preserves_bounded_contexts step_blob_hash ∧
  preserves_bounded_contexts step_self_balance ∧
  preserves_bounded_contexts step_mload ∧
  preserves_bounded_contexts (step_mstore op) ∧
  preserves_bounded_contexts step_jump ∧
  preserves_bounded_contexts step_jumpi ∧
  preserves_bounded_contexts (step_push n ws) ∧
  preserves_bounded_contexts step_pop ∧
  preserves_bounded_contexts (step_dup n) ∧
  preserves_bounded_contexts (step_swap n) ∧
  preserves_bounded_contexts (step_log n) ∧
  preserves_bounded_contexts (step_return b) ∧
  preserves_bounded_contexts step_self_destruct
Proof
  rw[step_binop_def, step_monop_def, step_modop_def, step_context_def,
     step_msgParams_def, step_txParams_def, step_exp_def,
     step_keccak256_def, step_sload_def, step_sstore_gas_consumption_def,
     step_sstore_def, step_balance_def, step_call_data_load_def,
     step_return_data_copy_def, step_ext_code_size_def,
     step_ext_code_copy_def, step_ext_code_hash_def, step_block_hash_def,
     step_blob_hash_def, step_self_balance_def, step_mload_def,
     step_mstore_def, step_jump_def, step_jumpi_def, step_push_def,
     step_pop_def, step_dup_def, step_swap_def, step_log_def,
     step_return_def, step_self_destruct_def, write_storage_def,
     write_transient_storage_def, read_memory_def]
  \\ pres_tac
QED

(* Creates. *)

Theorem preserves_bounded_contexts_create[simp]:
  preserves_bounded_contexts (abort_unuse n) ∧
  preserves_bounded_contexts (abort_create_exists a) ∧
  preserves_bounded_contexts (proceed_create a b v code g) ∧
  preserves_bounded_contexts (step_create two)
Proof
  rw[abort_unuse_def, abort_create_exists_def, proceed_create_def,
     step_create_def]
  \\ pres_tac
QED

(* Precompiles. *)

fun pres_with_tac thms =
  rpt (FIRST [irule preserves_bounded_contexts_get_current_context_bind,
              irule preserves_bounded_contexts_assert_bind,
              irule preserves_bounded_contexts_bind,
              irule preserves_bounded_contexts_ignore_bind,
              CASE_TAC, pairarg_tac] \\ rw (thms @ pres_simps));

Theorem preserves_bounded_contexts_precompile_ecrecover[simp]:
  preserves_bounded_contexts precompile_ecrecover
Proof
  rw[precompile_ecrecover_def] \\ pres_with_tac [length_pad_left]
QED

Theorem preserves_bounded_contexts_precompile_sha2_256[simp]:
  preserves_bounded_contexts precompile_sha2_256
Proof
  rw[precompile_sha2_256_def] \\ pres_with_tac []
QED

Theorem preserves_bounded_contexts_precompile_ripemd_160[simp]:
  preserves_bounded_contexts precompile_ripemd_160
Proof
  rw[precompile_ripemd_160_def] \\ pres_with_tac [length_pad_left]
QED

Theorem preserves_bounded_contexts_precompile_identity[simp]:
  preserves_bounded_contexts precompile_identity
Proof
  rw[precompile_identity_def, get_call_data_def] \\ pres_with_tac []
QED

Theorem preserves_bounded_contexts_precompile_ecpairing[simp]:
  preserves_bounded_contexts precompile_ecpairing
Proof
  rw[precompile_ecpairing_def] \\ pres_with_tac [length_pad_left]
QED

Theorem preserves_bounded_contexts_precompile_blake2f[simp]:
  preserves_bounded_contexts precompile_blake2f
Proof
  rw[precompile_blake2f_def] \\ pres_with_tac [LENGTH_blake2f]
QED

Theorem preserves_bounded_contexts_precompile_point_eval[simp]:
  preserves_bounded_contexts precompile_point_eval
Proof
  rw[precompile_point_eval_def] \\ pres_with_tac [LENGTH_point_eval_output]
QED

Theorem preserves_bounded_contexts_precompile_p256verify[simp]:
  preserves_bounded_contexts precompile_p256verify
Proof
  rw[precompile_p256verify_def] \\ pres_with_tac [length_pad_left]
QED

Theorem preserves_bounded_contexts_precompile_ecadd[simp]:
  preserves_bounded_contexts precompile_ecadd
Proof
  rw[precompile_ecadd_def] \\ pres_tac
  \\ imp_res_tac ecadd_lt
  \\ irule preserves_bounded_contexts_set_return_data
  \\ simp[LENGTH_bn254_coordinate]
QED

Theorem preserves_bounded_contexts_precompile_ecmul[simp]:
  preserves_bounded_contexts precompile_ecmul
Proof
  rw[precompile_ecmul_def] \\ pres_tac
  \\ imp_res_tac ecmul_lt
  \\ irule preserves_bounded_contexts_set_return_data
  \\ simp[LENGTH_bn254_coordinate]
QED

Theorem preserves_bounded_contexts_precompile_bls_g1add[simp]:
  preserves_bounded_contexts precompile_bls_g1add
Proof
  rw[precompile_bls_g1add_def] \\ pres_tac
  \\ imp_res_tac LENGTH_bls_outputs
  \\ irule preserves_bounded_contexts_set_return_data \\ simp[]
QED

Theorem preserves_bounded_contexts_precompile_bls_g1msm[simp]:
  preserves_bounded_contexts precompile_bls_g1msm
Proof
  rw[precompile_bls_g1msm_def] \\ pres_tac
  \\ imp_res_tac LENGTH_bls_outputs
  \\ irule preserves_bounded_contexts_set_return_data \\ simp[]
QED

Theorem preserves_bounded_contexts_precompile_bls_g2add[simp]:
  preserves_bounded_contexts precompile_bls_g2add
Proof
  rw[precompile_bls_g2add_def] \\ pres_tac
  \\ imp_res_tac LENGTH_bls_outputs
  \\ irule preserves_bounded_contexts_set_return_data \\ simp[]
QED

Theorem preserves_bounded_contexts_precompile_bls_g2msm[simp]:
  preserves_bounded_contexts precompile_bls_g2msm
Proof
  rw[precompile_bls_g2msm_def] \\ pres_tac
  \\ imp_res_tac LENGTH_bls_outputs
  \\ irule preserves_bounded_contexts_set_return_data \\ simp[]
QED

Theorem preserves_bounded_contexts_precompile_bls_pairing[simp]:
  preserves_bounded_contexts precompile_bls_pairing
Proof
  rw[precompile_bls_pairing_def] \\ pres_tac
  \\ imp_res_tac LENGTH_bls_outputs
  \\ irule preserves_bounded_contexts_set_return_data \\ simp[]
QED

Theorem preserves_bounded_contexts_precompile_bls_map_fp_to_g1[simp]:
  preserves_bounded_contexts precompile_bls_map_fp_to_g1
Proof
  rw[precompile_bls_map_fp_to_g1_def] \\ pres_tac
  \\ imp_res_tac LENGTH_bls_outputs
  \\ irule preserves_bounded_contexts_set_return_data \\ simp[]
QED

Theorem preserves_bounded_contexts_precompile_bls_map_fp2_to_g2[simp]:
  preserves_bounded_contexts precompile_bls_map_fp2_to_g2
Proof
  rw[precompile_bls_map_fp2_to_g2_def] \\ pres_tac
  \\ imp_res_tac LENGTH_bls_outputs
  \\ irule preserves_bounded_contexts_set_return_data \\ simp[]
QED

Theorem preserves_bounded_contexts_precompile_modexp[simp]:
  preserves_bounded_contexts precompile_modexp
Proof
  rw[precompile_modexp_def]
  \\ irule preserves_bounded_contexts_bind \\ rw[]
  \\ irule preserves_bounded_contexts_assert_bind \\ strip_tac
  \\ irule preserves_bounded_contexts_ignore_bind \\ simp[]
  \\ irule preserves_bounded_contexts_ignore_bind \\ simp[]
  \\ irule preserves_bounded_contexts_set_return_data
  \\ irule LESS_EQ_LESS_TRANS \\ qexists_tac `1024` \\ simp[]
  \\ rw[length_pad_right]
  \\ qmatch_goalsub_abbrev_tac
       `n2l 256 (modexp bb ee (l2n 256 (REVERSE (MAP w2n (take_pad_0 zz ll)))) 1)`
  \\ mp_tac (Q.INST [`b`|->`bb`,`e`|->`ee`,`z`|->`zz`,`ls`|->`ll`]
              (INST_TYPE [alpha |-> ``:8``] LENGTH_modexp_output))
  \\ unabbrev_all_tac \\ rw[]
QED

Theorem preserves_bounded_contexts_dispatch_precompiles[simp]:
  preserves_bounded_contexts (dispatch_precompiles a)
Proof
  rw[dispatch_precompiles_def, preserves_bounded_contexts_precompile_modexp]
QED

(* Calls. *)

Theorem preserves_bounded_contexts_call:
  sz < 2 ** 256 ⇒
  preserves_bounded_contexts
    (proceed_call op sender address value off sz code stipend outputTo)
Proof
  rw[proceed_call_def, read_memory_def] \\ pres_tac
QED

Theorem preserves_bounded_contexts_step_call[simp]:
  preserves_bounded_contexts (abort_call_value n) ∧
  preserves_bounded_contexts (step_call op)
Proof
  rw[abort_call_value_def, step_call_def]
  \\ pres_tac
  \\ irule preserves_bounded_contexts_call \\ rw[w2n_bytes32_lt]
QED

(* A step. *)

Theorem preserves_bounded_contexts_step_inst[simp]:
  preserves_bounded_contexts (step_inst op)
Proof
  Cases_on `op` \\ rw[step_inst_def] \\ pres_tac
QED

Theorem preserves_bounded_contexts_handlers[simp]:
  preserves_bounded_contexts (inc_pc_or_jump op) ∧
  preserves_bounded_contexts (pop_and_incorporate_context b) ∧
  preserves_bounded_contexts (handle_create e) ∧
  preserves_bounded_contexts (handle_exception e)
Proof
  rw[inc_pc_or_jump_def, pop_and_incorporate_context_def,
     handle_create_def, handle_exception_def, get_return_data_def]
  \\ pres_tac
QED

Theorem preserves_bounded_contexts_handle_step[simp]:
  preserves_bounded_contexts (handle_step e)
Proof
  rw[handle_step_def]
  \\ irule preserves_bounded_contexts_handle \\ rw[]
QED

Theorem preserves_bounded_contexts_step:
  preserves_bounded_contexts step
Proof
  rw[step_def] \\ irule preserves_bounded_contexts_handle \\ rw[]
  \\ pres_tac
QED

(* -------------------------------------------------------------------------
 * A step, and the initial state.
 * ------------------------------------------------------------------------- *)

Theorem step_returndata_bounded:
  returndata_bounded s ∧ calldata_bounded s ⇒
  returndata_bounded (SND (step s))
Proof
  strip_tac
  \\ `EVERY bounded_context (MAP FST (SND (step s)).contexts)`
       by (irule (REWRITE_RULE [preserves_bounded_contexts_def]
                    preserves_bounded_contexts_step)
           \\ simp[bounded_contexts_eq])
  \\ gvs[bounded_contexts_eq]
QED

Theorem initial_state_returndata_bounded:
  initial_state dom static chainId prevHashes blk accs tx = SOME s ⇒
  returndata_bounded s
Proof
  strip_tac \\ gvs[initial_state_def, AllCaseEqs()]
  \\ rpt (pairarg_tac \\ gvs[])
  \\ gvs[apply_intrinsic_cost_def, AllCaseEqs(), returndata_bounded_def]
QED
