Theory vfmCallMeterSafe
Ancestors vfmCallMeter vfmCallMeterProbe vfmExecution vfmContext vfmState vfmTypes
          arithmetic list

Definition call_meter_safe_def:
  call_meter_safe P m Q <=>
    !s r t. P (s:execution_state) /\ m s = (r,t) ==>
      Q r t /\
      (!e. r = INR e ==> e <> SOME Impossible /\ e <> SOME Unimplemented)
End

Theorem call_meter_safe_return:
  (!s. P s ==> Q (INL x) s) ==> call_meter_safe P (return x) Q
Proof
  simp[call_meter_safe_def, return_def]
QED

Theorem call_meter_safe_fail:
  e <> Impossible /\ e <> Unimplemented /\
  (!s. P s ==> Q (INR (SOME e)) s) ==>
  call_meter_safe P (fail e) Q
Proof
  simp[call_meter_safe_def, fail_def]
QED

Theorem call_meter_safe_consequence:
  call_meter_safe P m Q /\ (!s. P' s ==> P s) /\
  (!r s. Q r s ==> Q' r s) ==> call_meter_safe P' m Q'
Proof
  simp[call_meter_safe_def] >> metis_tac[]
QED

Theorem call_meter_safe_bind:
  call_meter_safe P g (\r s. case r of INL x => R x s | INR e => Q (INR e) s) /\
  (!x. call_meter_safe (R x) (f x) Q) ==>
  call_meter_safe P (bind g f) Q
Proof
  rewrite_tac[call_meter_safe_def] >> strip_tac >>
  map_every qx_gen_tac [`s`, `r`, `t`] >> strip_tac >>
  qpat_x_assum `!s r t. P s /\ _ ==> _`
    (qspecl_then [`s`, `FST (g s)`, `SND (g s)`] mp_tac) >>
  Cases_on `g s` >> Cases_on `q` >>
  gvs[bind_def] >> metis_tac[]
QED

Theorem call_meter_safe_ignore_bind:
  call_meter_safe P g (\r s. case r of INL x => R s | INR e => Q (INR e) s) /\
  call_meter_safe R f Q ==>
  call_meter_safe P (ignore_bind g f) Q
Proof
  simp[ignore_bind_def] >> strip_tac >> irule call_meter_safe_bind >>
  qexists `\x s. R s` >> simp[ETA_THM]
QED

Theorem call_meter_safe_bind_invariant:
  call_meter_safe P g (\r s. Inv s) /\
  (!x. call_meter_safe Inv (f x) (\r s. Inv s)) ==>
  call_meter_safe P (bind g f) (\r s. Inv s)
Proof
  strip_tac >> irule call_meter_safe_bind >> qexists `\x s. Inv s` >>
  gvs[call_meter_safe_def] >> rpt strip_tac >> Cases_on `r` >> gvs[] >> metis_tac[]
QED

Theorem call_meter_safe_from_result:
  (!s r t. P s /\ m s = (r,t) ==> call_meter_result c rb rest t) /\
  (!s e t. P s /\ m s = (INR e,t) ==>
    e <> SOME Impossible /\ e <> SOME Unimplemented) ==>
  call_meter_safe P m (\r t. call_meter_result c rb rest t)
Proof
  simp[call_meter_safe_def] >> metis_tac[]
QED

Theorem call_meter_safe_consume:
  call_meter_safe
    (\s. s.contexts = (c,rb)::rest /\ call_meter_backed c /\
         c.gasUsed <= c.msgParams.gasLimit)
    (consume_gas amount) (\r t. call_meter_result c rb rest t)
Proof
  rewrite_tac[call_meter_safe_def] >> rpt gen_tac >> strip_tac >>
  gvs[] >> conj_tac
  >- (irule call_meter_consume_result >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[consume_gas_def, get_current_context_def, set_current_context_def,
      bind_def, ignore_bind_def, return_def, assert_def, fail_def, AllCaseEqs()]
QED

(* An early OutOfGas bypasses its continuation but still has a postcondition. *)
Theorem call_meter_safe_early_failure:
  call_meter_safe P (bind (fail OutOfGas) f) (\r t. P t)
Proof
  irule call_meter_safe_bind >> qexists `\x s. F` >>
  simp[call_meter_safe_def, fail_def]
QED

Theorem call_meter_safe_consume_return:
  call_meter_safe
    (\s. s.contexts = (c,rb)::rest /\ call_meter_backed c /\
         c.gasUsed <= c.msgParams.gasLimit)
    (bind (consume_gas amount) (\x. return value))
    (\r t. call_meter_result c rb rest t)
Proof
  irule call_meter_safe_bind_invariant >>
  simp[call_meter_safe_consume, call_meter_safe_return]
QED

Theorem call_meter_safe_return_grant:
  call_meter_safe (call_meter_grant_result c amount rb rest)
    (restore_child_gas amount reservoir)
    (\r t. r = INL () /\ call_meter_result c rb rest t)
Proof
  rewrite_tac[call_meter_safe_def] >> rpt gen_tac >> strip_tac >>
  drule_all call_meter_return_grant >> simp[]
QED
