open HolKernel boolLib bossLib Parse
     vfmStateTheory vfmContextTheory vfmExecutionTheory;

val () = new_theory "vfmExecutionInvariants";

(* TODO: this probably needs to depend on block number (for hardforks) *)
Definition wf_account_state_def:
  wf_account_state a
  ⇔ a.nonce < 2 ** 64                  (* https://eips.ethereum.org/EIPS/eip-2681 *)
  ∧ LENGTH a.code <= 2 ** 14 + 2 ** 13 (* https://eips.ethereum.org/EIPS/eip-170 *)
End

Theorem wf_empty_account_state[simp]:
  wf_account_state empty_account_state
Proof
  rw[empty_account_state_def, wf_account_state_def]
QED

Definition wf_accounts_def:
  wf_accounts a ⇔ ∀x. wf_account_state (a x)
End

Definition wf_context_def:
  wf_context c ⇔
    LENGTH c.stack ≤ stack_limit ∧
    c.gasUsed ≤ c.msgParams.gasLimit
End

Definition wf_state_def:
  wf_state s ⇔
    s.contexts ≠ [] ∧
    LENGTH s.contexts ≤ context_limit ∧
    EVERY wf_context s.contexts ∧
    wf_accounts s.rollback.accounts
End

Theorem wf_initial_context[simp]:
  wf_context (initial_context rb callee c s rd t)
Proof
  rw[wf_context_def]
QED

Theorem wf_context_apply_intrinsic_cost:
  wf_context (apply_intrinsic_cost a c) =
  (wf_context c ∧
   c.gasUsed ≤ c.msgParams.gasLimit - intrinsic_cost a c.msgParams)
Proof
  rw[apply_intrinsic_cost_def, wf_context_def]
QED

Theorem wf_initial_state:
  wf_accounts a ∧ initial_state d st c h b a t = SOME s
  ⇒
  wf_state s
Proof
  rw[wf_accounts_def, wf_state_def, initial_state_def,
     pre_transaction_updates_def, update_account_def,
     initial_rollback_def, code_from_tx_def, lookup_account_def,
     wf_context_apply_intrinsic_cost] \\ rw[]
  \\ gs[wf_account_state_def, combinTheory.APPLY_UPDATE_THM]
  \\ rw[wf_context_apply_intrinsic_cost]
QED

Definition preserves_wf_state_def:
  preserves_wf_state (m: execution_state -> α execution_result) =
  ∀s. wf_state s ⇒ wf_state (SND (m s))
End

Theorem preserves_wf_state_handle[simp]:
  preserves_wf_state f ∧
  (∀e. preserves_wf_state (h e))
  ⇒
  preserves_wf_state (handle f h)
Proof
  rw[preserves_wf_state_def, handle_def]
  \\ CASE_TAC \\ gs[]
  \\ CASE_TAC \\ gs[]
  \\ last_x_assum drule \\ rw[]
QED

Theorem preserves_wf_state_bind_gen:
  preserves_wf_state g ∧
  (∀s a s'. g s = (INL a, s') ⇒ p a) ∧
  (∀x. p x ⇒ preserves_wf_state (f x))
  ⇒
  preserves_wf_state (bind g f)
Proof
  rw[preserves_wf_state_def, bind_def]
  \\ CASE_TAC
  \\ last_x_assum drule \\ rw[]
  \\ CASE_TAC \\ rw[]
  \\ last_x_assum drule \\ rw[]
QED

Theorem preserves_wf_state_bind:
  preserves_wf_state g ∧
  (∀x. preserves_wf_state (f x))
  ⇒
  preserves_wf_state (bind g f)
Proof
  strip_tac
  \\ irule preserves_wf_state_bind_gen \\ rw[]
  \\ qexists_tac`K T` \\ rw[]
QED

Theorem preserves_wf_state_ignore_bind:
  preserves_wf_state g ∧ preserves_wf_state f
  ⇒
  preserves_wf_state (ignore_bind g f)
Proof
  rw[ignore_bind_def]
  \\ irule preserves_wf_state_bind
  \\ rw[]
QED

Theorem wf_state_step[simp]:
  preserves_wf_state step
Proof
  rw[step_def]
  \\ irule preserves_wf_state_handle
  \\ cheat
QED

val () = export_theory();
