Theory vfmRunFrame
Ancestors
  arithmetic combin list option pair sum While
  vfmExecution vfmExecutionProp vfmDecreasesGas vfmStepLength
  vfmHandleStep vfmContextLength vfmWfState
Libs
  BasicProvers

Theorem run_frame_inr:
  run_frame es = SOME (r, es1) ⇒ ISR r
Proof
  simp[run_frame_def] >> strip_tac >>
  drule OWHILE_ENDCOND >> Cases_on `r` >> simp[]
QED

Theorem run_frame_length:
  wf_state es ∧ run_frame es = SOME (INR e, es1) ∧ ¬vfm_abort e ⇒
  LENGTH es1.contexts = LENGTH es.contexts
Proof
  cheat
QED

Theorem run_frame_call:
  wf_state es ∧ run_frame es = SOME (INR e, es1) ∧ ¬vfm_abort e ⇒
  run_call es = SOME (handle_exception e es1)
Proof
  cheat
QED

Theorem run_call_imp_run_frame:
  run_call es = SOME r ⇒
  ∃e es1. run_frame es = SOME (INR e, es1)
Proof
  cheat
QED
