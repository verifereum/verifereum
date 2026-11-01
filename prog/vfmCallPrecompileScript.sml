Theory vfmCallPrecompile
Ancestors vfmCallMeterOps vfmCallMeterSafe vfmCallMeter vfmCallBudget
          vfmCallMeterBase vfmExecution vfmContext vfmState vfmTypes arithmetic list

Theorem call_meter_result_trans:
  call_meter_result c rb rest s /\ s.contexts = (d,rb)::rest /\
  call_meter_result d rb rest t ==> call_meter_result c rb rest t
Proof
  simp[call_meter_result_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[LESS_EQ_TRANS]
QED

(* A fixed-tail contract may be used after any earlier spend in the frame. *)
Theorem call_meter_safe_result_lift:
  (!d. call_meter_safe (call_meter_ready d rb rest) m
         (\r t. call_meter_result d rb rest t)) ==>
  call_meter_safe (call_meter_result c rb rest) m
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[call_meter_safe_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `?d. s.contexts = (d,rb)::rest /\ call_meter_backed d /\
       d.gasUsed <= d.msgParams.gasLimit` by metis_tac[call_meter_result_def] >>
  qpat_x_assum `!d. _` (qspec_then `d` mp_tac) >>
  disch_then (qspecl_then [`s`, `r`, `t`] mp_tac) >>
  simp[call_meter_ready_def] >> strip_tac >>
  irule call_meter_result_trans >> metis_tac[]
QED

Theorem call_meter_safe_consume_inv:
  call_meter_safe (call_meter_result c rb rest) (consume_gas n)
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_result_lift >> gen_tac >>
  rewrite_tac[lambdify call_meter_ready_def] >> BETA_TAC >> irule call_meter_safe_consume
QED

Theorem call_meter_safe_data_inv:
  call_meter_safe (call_meter_result c rb rest) get_call_data
    (\r t. call_meter_result c rb rest t)
Proof
  simp[call_meter_safe_def, get_call_data_def, get_current_context_def,
       bind_def, return_def, call_meter_result_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem call_meter_safe_output_inv:
  call_meter_safe (call_meter_result c rb rest) (set_return_data bytes)
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_result_lift >> simp[call_meter_safe_set_return_data]
QED

Theorem call_meter_safe_finish_inv:
  call_meter_safe (call_meter_result c rb rest) finish
    (\r t. call_meter_result c rb rest t)
Proof
  simp[call_meter_safe_def, finish_def]
QED

Theorem call_meter_safe_ignore_invariant:
  call_meter_safe P g (\r s. Inv s) /\
  call_meter_safe Inv f (\r s. Inv s) ==>
  call_meter_safe P (ignore_bind g f) (\r s. Inv s)
Proof
  simp[ignore_bind_def] >> strip_tac >>
  irule call_meter_safe_bind_invariant >> simp[]
QED

Theorem call_meter_safe_output_finish:
  call_meter_safe (call_meter_result c rb rest) (ignore_bind (set_return_data bytes) finish)
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_ignore_invariant >>
  simp[call_meter_safe_output_inv, call_meter_safe_finish_inv]
QED

Theorem call_meter_safe_precompile_identity:
  call_meter_safe (call_meter_result c rb rest) precompile_identity
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[precompile_identity_def] >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> simp[LET_THM] >> irule call_meter_safe_ignore_invariant >>
      simp[call_meter_safe_consume_inv, call_meter_safe_output_finish]) >>
  simp[call_meter_safe_data_inv]
QED

Theorem call_meter_safe_optional_output:
  call_meter_safe (call_meter_result c rb rest)
    (case output of NONE => fail OutOfGas
     | SOME bytes => ignore_bind (set_return_data bytes) finish)
    (\r t. call_meter_result c rb rest t)
Proof
  Cases_on `output` >> simp[call_meter_safe_output_finish] >>
  irule call_meter_safe_fail >> simp[]
QED

Theorem call_meter_safe_precompile_spend:
  (!input. call_meter_safe (call_meter_result c rb rest) (f input)
      (\r t. call_meter_result c rb rest t)) ==>
  call_meter_safe (call_meter_result c rb rest)
    (bind get_call_data (\input. ignore_bind (consume_gas (cost input)) (f input)))
    (\r t. call_meter_result c rb rest t)
Proof
  strip_tac >> irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule call_meter_safe_ignore_invariant >>
      simp[call_meter_safe_consume_inv]) >>
  simp[call_meter_safe_data_inv]
QED

Theorem call_meter_safe_precompile_bls_g1add:
  call_meter_safe (call_meter_result c rb rest) precompile_bls_g1add
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[precompile_bls_g1add_def] >>
  ho_match_mp_tac call_meter_safe_precompile_spend >>
  simp[call_meter_safe_optional_output]
QED

Theorem call_meter_safe_precompile_bls_g1msm:
  call_meter_safe (call_meter_result c rb rest) precompile_bls_g1msm
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[precompile_bls_g1msm_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac call_meter_safe_precompile_spend >>
  simp[call_meter_safe_optional_output]
QED

Theorem call_meter_safe_precompile_bls_g2add:
  call_meter_safe (call_meter_result c rb rest) precompile_bls_g2add
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[precompile_bls_g2add_def] >>
  ho_match_mp_tac call_meter_safe_precompile_spend >>
  simp[call_meter_safe_optional_output]
QED

Theorem call_meter_safe_precompile_bls_g2msm:
  call_meter_safe (call_meter_result c rb rest) precompile_bls_g2msm
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[precompile_bls_g2msm_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac call_meter_safe_precompile_spend >>
  simp[call_meter_safe_optional_output]
QED

Theorem call_meter_safe_precompile_bls_pairing:
  call_meter_safe (call_meter_result c rb rest) precompile_bls_pairing
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[precompile_bls_pairing_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac call_meter_safe_precompile_spend >>
  simp[call_meter_safe_optional_output]
QED

Theorem call_meter_safe_precompile_bls_map_fp_to_g1:
  call_meter_safe (call_meter_result c rb rest) precompile_bls_map_fp_to_g1
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[precompile_bls_map_fp_to_g1_def] >>
  ho_match_mp_tac call_meter_safe_precompile_spend >>
  simp[call_meter_safe_optional_output]
QED

Theorem call_meter_safe_precompile_bls_map_fp2_to_g2:
  call_meter_safe (call_meter_result c rb rest) precompile_bls_map_fp2_to_g2
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[precompile_bls_map_fp2_to_g2_def] >>
  ho_match_mp_tac call_meter_safe_precompile_spend >>
  simp[call_meter_safe_optional_output]
QED

Theorem call_meter_safe_precompile_sha2_256:
  call_meter_safe (call_meter_result c rb rest) precompile_sha2_256
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[precompile_sha2_256_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac call_meter_safe_precompile_spend >>
  simp[call_meter_safe_output_finish]
QED

Theorem call_meter_safe_option_case:
  e <> Impossible /\ e <> Unimplemented ==>
  call_meter_safe (call_meter_result c rb rest)
    (case output of NONE => fail e
     | SOME x => ignore_bind (set_return_data (f x)) finish)
    (\r t. call_meter_result c rb rest t)
Proof
  strip_tac >> Cases_on `output` >> simp[call_meter_safe_output_finish] >>
  irule call_meter_safe_fail >> simp[]
QED

Theorem call_meter_safe_precompile_ripemd_160:
  call_meter_safe (call_meter_result c rb rest) precompile_ripemd_160
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[precompile_ripemd_160_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac call_meter_safe_precompile_spend >> gen_tac >>
  ho_match_mp_tac call_meter_safe_option_case >> simp[]
QED

Theorem call_meter_safe_precompile_ecadd:
  call_meter_safe (call_meter_result c rb rest) precompile_ecadd
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[precompile_ecadd_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac call_meter_safe_precompile_spend >> gen_tac >>
  CASE_TAC >> simp[call_meter_safe_fail] >>
  rename1 `ecadd _ _ = SOME xy` >> PairCases_on `xy` >>
  simp[call_meter_safe_output_finish]
QED

Theorem call_meter_safe_precompile_ecmul:
  call_meter_safe (call_meter_result c rb rest) precompile_ecmul
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[precompile_ecmul_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac call_meter_safe_precompile_spend >> gen_tac >>
  CASE_TAC >> simp[call_meter_safe_fail] >>
  rename1 `ecmul _ _ = SOME xy` >> PairCases_on `xy` >>
  simp[call_meter_safe_output_finish]
QED

Theorem call_meter_safe_precompile_ecpairing:
  call_meter_safe (call_meter_result c rb rest) precompile_ecpairing
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[precompile_ecpairing_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac call_meter_safe_precompile_spend >> gen_tac >>
  IF_CASES_TAC >> simp[call_meter_safe_fail] >>
  ho_match_mp_tac call_meter_safe_option_case >> simp[]
QED

Theorem call_meter_safe_precompile_ecrecover:
  call_meter_safe (call_meter_result c rb rest) precompile_ecrecover
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[precompile_ecrecover_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac call_meter_safe_precompile_spend >> gen_tac >>
  CASE_TAC >> simp[call_meter_safe_finish_inv, call_meter_safe_output_finish]
QED

Theorem call_meter_safe_precompile_p256verify:
  call_meter_safe (call_meter_result c rb rest) precompile_p256verify
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[precompile_p256verify_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac call_meter_safe_precompile_spend >> gen_tac >>
  IF_CASES_TAC >> simp[call_meter_safe_finish_inv] >>
  IF_CASES_TAC >> simp[call_meter_safe_finish_inv, call_meter_safe_output_finish]
QED

Theorem call_meter_safe_precompile_modexp:
  call_meter_safe (call_meter_result c rb rest) precompile_modexp
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[precompile_modexp_def] >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
      irule call_meter_safe_ignore_invariant >>
      simp[call_meter_safe_assert] >>
      irule call_meter_safe_ignore_invariant >>
      simp[call_meter_safe_consume_inv, call_meter_safe_output_finish]) >>
  simp[call_meter_safe_data_inv]
QED

Theorem call_meter_safe_precompile_blake2f:
  call_meter_safe (call_meter_result c rb rest) precompile_blake2f
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[precompile_blake2f_def] >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> IF_CASES_TAC >> simp[call_meter_safe_fail] >>
      pure_rewrite_tac[LET_THM] >> BETA_TAC >>
      irule call_meter_safe_ignore_invariant >>
      simp[call_meter_safe_consume_inv] >>
      IF_CASES_TAC >> simp[call_meter_safe_fail, call_meter_safe_output_finish]) >>
  simp[call_meter_safe_data_inv]
QED

Theorem call_meter_safe_precompile_point_eval:
  call_meter_safe (call_meter_result c rb rest) precompile_point_eval
    (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[precompile_point_eval_def] >>
  irule call_meter_safe_bind_invariant >> conj_tac
  >- (gen_tac >> BETA_TAC >> IF_CASES_TAC >> simp[call_meter_safe_fail] >>
      pure_rewrite_tac[LET_THM] >> BETA_TAC >>
      irule call_meter_safe_ignore_invariant >> simp[call_meter_safe_consume_inv] >>
      irule call_meter_safe_ignore_invariant >> simp[call_meter_safe_assert] >>
      irule call_meter_safe_ignore_invariant >> simp[call_meter_safe_assert] >>
      ntac 2 CASE_TAC >> simp[call_meter_safe_fail] >>
      irule call_meter_safe_ignore_invariant >>
      simp[call_meter_safe_assert, call_meter_safe_output_finish]) >>
  simp[call_meter_safe_data_inv]
QED

Theorem call_meter_precompile_addresses[local]:
  precompile_addresses = fset_ABS
    [0x100w; 0x1w; 0x2w; 0x3w; 0x4w; 0x5w; 0x6w; 0x7w; 0x8w; 0x9w;
     0xaw; 0xbw; 0xcw; 0xdw; 0xew; 0xfw; 0x10w; 0x11w]
Proof
  rewrite_tac[precompile_addresses_def] >> AP_TERM_TAC >> EVAL_TAC
QED

Theorem call_meter_safe_dispatch_precompiles:
  fIN addr precompile_addresses ==>
  call_meter_safe (call_meter_result c rb rest) (dispatch_precompiles addr)
    (\r t. call_meter_result c rb rest t)
Proof
  simp[call_meter_precompile_addresses, finite_setTheory.fIN_fset_ABS] >>
  strip_tac >> gvs[SF wordsLib.SIZES_ss, dispatch_precompiles_def,
    call_meter_safe_precompile_identity, call_meter_safe_precompile_ecrecover,
    call_meter_safe_precompile_sha2_256, call_meter_safe_precompile_ripemd_160,
    call_meter_safe_precompile_modexp, call_meter_safe_precompile_ecadd,
    call_meter_safe_precompile_ecmul, call_meter_safe_precompile_ecpairing,
    call_meter_safe_precompile_blake2f, call_meter_safe_precompile_point_eval,
    call_meter_safe_precompile_bls_g1add, call_meter_safe_precompile_bls_g1msm,
    call_meter_safe_precompile_bls_g2add, call_meter_safe_precompile_bls_g2msm,
    call_meter_safe_precompile_bls_pairing, call_meter_safe_precompile_bls_map_fp_to_g1,
    call_meter_safe_precompile_bls_map_fp2_to_g2, call_meter_safe_precompile_p256verify]
QED

Theorem call_meter_dispatch_result:
  s.contexts = (c,rb)::rest /\ call_meter_backed c /\
  c.gasUsed <= c.msgParams.gasLimit /\ fIN addr precompile_addresses /\
  dispatch_precompiles addr s = (r,t) ==>
  call_meter_result c rb rest t /\
  (!e. r = INR e ==> e <> SOME Impossible /\ e <> SOME Unimplemented)
Proof
  rpt strip_tac >>
  drule call_meter_safe_dispatch_precompiles >>
  rewrite_tac[call_meter_safe_def] >>
  strip_tac >>
  `call_meter_result c rb rest s` by metis_tac[call_meter_result_same] >>
  first_x_assum drule_all >> simp[]
QED

Theorem call_meter_dispatch_budget:
  call_meter_budget n grant s /\ n <= LENGTH s.contexts /\
  s.contexts = (c,rb)::rest /\ call_meter_backed c /\
  c.gasUsed <= c.msgParams.gasLimit /\ fIN addr precompile_addresses /\
  dispatch_precompiles addr s = (r,t) ==>
  call_meter_budget n grant t /\
  (!e. r = INR e ==> e <> SOME Impossible /\ e <> SOME Unimplemented)
Proof
  rpt gen_tac >> strip_tac >> drule_all call_meter_dispatch_result >> strip_tac >>
  simp[] >> irule call_meter_result_budget >> metis_tac[]
QED
