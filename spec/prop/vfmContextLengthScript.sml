(* Context-stack length theorems for run and run_call.
 * Non-abort termination exits at the relevant frame boundary. *)
Theory vfmContextLength
Ancestors
  arithmetic combin list pair pred_set finite_set rich_list
  While vfmState vfmContext vfmExecution vfmExecutionProp
  vfmStaticCalls vfmTxParams vfmDomainSeparation vfmDecreasesGas
  vfmSameFrame vfmStepLength vfmMsdomainPreserved vfmHandleStep
  vfmRunWithinFrame vfmRunCall
Libs
  BasicProvers dep_rewrite

(* handle_step length on non-abort INR outputs. *)

Theorem handle_step_inr_not_abort_length:
  handle_step e s = (INR e', s') ∧ s.contexts ≠ [] ∧ EVERY (wf_context o FST) s.contexts ∧ ¬vfm_abort e ⇒
    if LENGTH s.contexts ≥ 2 then LENGTH s'.contexts = LENGTH s.contexts - 1
    else LENGTH s'.contexts = LENGTH s.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_step_inr_not_abort_length_bound:
  handle_step e s = (INR e', s') ∧ s.contexts ≠ [] ∧ EVERY (wf_context o FST) s.contexts ∧ ¬vfm_abort e ⇒
    LENGTH s'.contexts = LENGTH s.contexts ∨
    LENGTH s'.contexts + 1 = LENGTH s.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

(* step length on non-abort INR outputs. *)

Theorem step_inr_not_abort_length:
  step s = (INR e, s') ∧ s.contexts ≠ [] ∧ EVERY (wf_context o FST) s.contexts ∧
  outputTo_consistent s ∧ ¬vfm_abort e ⇒
    LENGTH s'.contexts = LENGTH s.contexts ∨
    LENGTH s'.contexts + 1 = LENGTH s.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

(* At depth ≥ 2, non-abort handle_step returns INL. *)

Theorem handle_step_not_abort_returns_inl:
  handle_step e s = (q, s') ∧ LENGTH s.contexts ≥ 2 ∧
  EVERY (wf_context o FST) s.contexts ∧ stack_room_ok s ∧ gas_stack_ok s ∧
  ¬vfm_abort e ⇒
    ISL q
Proof
  cheat  (* SCAFFOLD *)
QED

(* A step cannot return non-abort INR at depth ≥ 2. *)

Theorem step_ge2_inr_is_abort:
  step s = (INR e, s') ∧ LENGTH s.contexts ≥ 2 ∧
  wf_state s ∧ outputTo_consistent s ∧ ¬vfm_abort e ⇒
    F
Proof
  cheat  (* SCAFFOLD *)
QED

(* run terminates at depth 1 under non-abort termination. *)

Theorem run_contexts_length_1:
  run s = SOME (r, es') ∧ wf_state s ∧ (∀e. r = INR e ⇒ ¬vfm_abort e)
  ⇒ LENGTH es'.contexts = 1
Proof
  cheat  (* SCAFFOLD *)
QED

(* Single-context convenience form: *)
Theorem run_length_1_single:
  es.contexts = [(ctx, es.rollback)] ∧ wf_context ctx ∧
  wf_accounts es.rollback.accounts ∧
  outputTo_consistent_ctx ctx ∧
  run es = SOME (r, es') ∧ (∀e. r = INR e ⇒ ¬vfm_abort e) ⇒
    LENGTH es'.contexts = 1
Proof
  cheat  (* SCAFFOLD *)
QED

(* run_call exits at the starting-frame boundary. *)

Theorem run_call_inr_length:
  wf_state es ∧ run_call es = SOME (INR e, es') ∧ ¬vfm_abort e ⇒
    LENGTH es'.contexts = LENGTH es.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_length_not_drop_more_than_one:
  wf_state s ∧ step s = (r, s') ⇒
    LENGTH s.contexts ≤ LENGTH s'.contexts + 1
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_call_inl_length:
  wf_state es ∧ run_call es = SOME (INL (), es') ⇒
    LENGTH es'.contexts + 1 = LENGTH es.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_call_length:
  wf_state es ∧ run_call es = SOME (r, es') ∧
  (∀e. r = INR e ⇒ ¬vfm_abort e) ⇒
    case r of
    | INR e => LENGTH es'.contexts = LENGTH es.contexts
    | INL () => LENGTH es'.contexts + 1 = LENGTH es.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

(* At starting depth ≥ 2, INR termination must be aborting. *)
Theorem run_call_inr_requires_abort_ge2:
  LENGTH es.contexts ≥ 2 ∧ wf_state es ∧
  run_call es = SOME (INR e, es')
  ⇒ vfm_abort e
Proof
  cheat  (* SCAFFOLD *)
QED

(* Single-context convenience form: *)
Theorem run_call_inr_length_single:
  outputTo_consistent_ctx ctx ∧ wf_context ctx ∧ ctx.jumpDest = NONE ∧
  wf_accounts es.rollback.accounts ∧
  es.contexts = [(ctx, es.rollback)] ∧
  run_call es = SOME (INR e, es') ∧ ¬vfm_abort e ⇒
    LENGTH es'.contexts = 1
Proof
  cheat  (* SCAFFOLD *)
QED
