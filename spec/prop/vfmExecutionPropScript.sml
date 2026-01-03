Theory vfmExecutionProp
Ancestors
  combin pair list finite_map While
  vfmConstants vfmOperation vfmState vfmContext vfmExecution
Libs
  BasicProvers wordsLib

Theorem FLOOKUP_parse_code_SOME_less_LENGTH:
  ∀pc fm code x i.
    FLOOKUP (parse_code pc fm code) x = SOME i ⇒
    x ∈ FDOM fm ∨ x < pc + LENGTH code
Proof
  ho_match_mp_tac parse_code_ind
  \\ rpt gen_tac \\ strip_tac
  \\ rpt gen_tac \\ strip_tac
  \\ Cases_on`NULL code` \\ gvs[NULL_EQ]
  >- gvs[Once parse_code_def, TO_FLOOKUP]
  \\ qhdtm_x_assum`FLOOKUP`mp_tac
  \\ rw[Once parse_code_def, NULL_EQ]
  \\ first_x_assum drule
  \\ strip_tac \\ gvs[]
  \\ gvs[NULL_EQ, FLOOKUP_UPDATE]
  >- (Cases_on`code` \\ gs[])
  \\ qmatch_asmsub_abbrev_tac`pc + l`
  \\ Cases_on`l < LENGTH code` \\ gvs[]
  \\ Cases_on`parse_opcode code`  \\ gvs[]
  >- (gvs[opcode_def,Abbr`l`] \\ Cases_on`code` \\ gvs[])
  \\ gvs[DROP_LENGTH_TOO_LONG]
  \\ gs[Once parse_code_def]
  \\ gs[FLOOKUP_UPDATE]
  \\ Cases_on`pc = x` \\ gvs[]
  >- (Cases_on`code` \\ gs[])
  \\ gs[TO_FLOOKUP]
QED

(* TODO: move to another theory? *)

Type execution = “:execution_state -> α execution_result”;

Theorem return_bind[simp]:
  bind (return x) f = f x
Proof
  rw[bind_def, return_def, FUN_EQ_THM]
QED

Theorem return_ignore_bind[simp]:
  ignore_bind (return x) f = f
Proof
  rw[ignore_bind_def, return_def]
QED

Theorem bind_assoc[simp]:
  bind (bind x f) g =
  bind x (λa. bind (f a) g)
Proof
  rw[bind_def, FUN_EQ_THM]
  \\ CASE_TAC \\ rw[]
  \\ CASE_TAC \\ rw[]
QED

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

Theorem wf_accounts_transfer_value[simp]:
  wf_accounts a ⇒
  wf_accounts (transfer_value x y z a)
Proof
  rw[wf_accounts_def, wf_account_state_def, transfer_value_def,
     update_account_def, APPLY_UPDATE_THM]
  \\ rw[lookup_account_def]
QED

Theorem wf_accounts_update_account:
  wf_accounts a ∧ wf_account_state x ⇒
  wf_accounts (update_account addr x a)
Proof
  rw[wf_accounts_def, update_account_def, APPLY_UPDATE_THM]
  \\ rw[]
QED

Definition wf_context_def:
  wf_context c ⇔
    LENGTH c.stack ≤ stack_limit ∧
    c.gasUsed ≤ c.msgParams.gasLimit ∧
    c.msgParams.parsed = parse_code 0 FEMPTY c.msgParams.code
End

Definition all_accounts_def:
  all_accounts s =
  s.rollback.accounts :: (MAP (λcr. (SND cr).accounts) s.contexts)
End

Definition wf_state_def:
  wf_state s ⇔
    s.contexts ≠ [] ∧
    LENGTH s.contexts ≤ SUC context_limit ∧
    EVERY (wf_context o FST) s.contexts ∧
    EVERY wf_accounts (all_accounts s)
End

Definition ok_state_def:
  ok_state s ⇔
    EVERY (wf_context o FST) s.contexts
End

Theorem wf_initial_context[simp]:
  wf_context (initial_context callee c s rd t)
Proof
  rw[wf_context_def, initial_msg_params_def]
QED

Theorem wf_context_apply_intrinsic_cost:
  apply_intrinsic_cost a n c = SOME c' ⇒
  wf_context c' =
  (wf_context c ∧
   c.gasUsed ≤ c.msgParams.gasLimit - intrinsic_cost a n c.msgParams)
Proof
  rw[apply_intrinsic_cost_def, wf_context_def] \\ rw[EQ_IMP_THM]
QED

Theorem wf_context_with_addRefund[simp]:
  wf_context (ctxt with addRefund updated_by f) = wf_context ctxt
Proof
  rw[wf_context_def]
QED

Theorem LENGTH_make_delegation[simp]:
  LENGTH (make_delegation x) = 23
Proof
  rw[make_delegation_def, delegation_prefix_def]
QED

Theorem wf_accounts_process_authorizations:
  ∀chainId authList a accesses r x y z.
    wf_accounts a ∧ process_authorizations chainId authList a accesses r = (x,y,z) ⇒
    wf_accounts x
Proof
  Induct_on `authList` \\ rw[process_authorizations_def] \\ simp[]
  \\ pop_assum mp_tac
  \\ CONV_TAC(PATH_CONV"lrlr"(ONCE_REWRITE_CONV[GSYM LET_THM]))
  \\ LET_ELIM_TAC
  \\ first_x_assum irule
  \\ goal_assum $ drule_at(Pos(Lib.first is_eq))
  \\ gvs[process_authorization_def]
  \\ gvs[wf_accounts_def, wf_account_state_def, CaseEq"bool",
         update_account_def, APPLY_UPDATE_THM, lookup_account_def]
  \\ rw[]
QED

Theorem wf_accounts_pre_transaction_updates:
  wf_accounts a ∧ pre_transaction_updates a b c = SOME e ⇒
  wf_accounts e
Proof
  rw[pre_transaction_updates_def, update_account_def,
     lookup_account_def, APPLY_UPDATE_THM, wf_accounts_def,
     wf_account_state_def]
  \\ gvs[APPLY_UPDATE_THM] \\ rw[]
QED

Theorem wf_initial_state:
  wf_accounts a ∧ initial_state d st c h b a t = SOME s
  ⇒
  wf_state s
Proof
  strip_tac
  \\ gvs[initial_state_def, CaseEq"option"]
  \\ pairarg_tac \\ gvs[]
  \\ pairarg_tac
  \\ gvs[CaseEq"option"]
  \\ simp[wf_state_def]
  \\ simp[all_accounts_def]
  \\ conj_tac
  >- ( drule wf_context_apply_intrinsic_cost \\ simp[] )
  \\ simp[initial_rollback_def]
  \\ irule wf_accounts_process_authorizations
  \\ goal_assum $ drule_at(Pos(Lib.first is_eq))
  \\ irule wf_accounts_pre_transaction_updates
  \\ goal_assum $ drule_at(Pos(Lib.first is_eq))
  \\ rw[]
QED

Theorem pop_and_incorporate_context_preserves:
  LENGTH st.contexts > 1 ⇒
  (SND (pop_and_incorporate_context b st)).contexts ≠ []
Proof
  strip_tac \\ rw[pop_and_incorporate_context_def]
  \\ rw[bind_def, get_gas_left_def, pop_context_def]
  \\ rw[get_current_context_def]
  >- gvs[]
  >- (
    simp[return_def]
    \\ simp[ignore_bind_def, bind_def, unuse_gas_def,
            set_current_context_def, push_logs_def, update_gas_refund_def,
            set_rollback_def, return_def]
    \\ simp[get_current_context_def]
    \\ `TL st.contexts ≠ []` by (
      strip_tac \\ pop_assum(strip_assume_tac o Q.AP_TERM`LENGTH`) \\ gvs[])
    \\ simp[]
    \\ simp[return_def]
    \\ simp[assert_def, fail_def]
    \\ CASE_TAC
    >- (CASE_TAC \\ simp[set_rollback_def, bind_def,
            get_current_context_def, set_current_context_def, fail_def,
            return_def])
    >- simp[])
QED

(* --------------------------------------------------------------------------
   Preservation of non-empty contexts
   -------------------------------------------------------------------------- *)

(* Layer 1: Primitives *)

Theorem return_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (return x s)).contexts ≠ []
Proof
  rw[return_def]
QED

Theorem fail_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (fail e s)).contexts ≠ []
Proof
  rw[fail_def]
QED

Theorem assert_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (assert b e s)).contexts ≠ []
Proof
  rw[assert_def]
QED

(* Layer 2: Core state operations *)

Theorem get_current_context_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (get_current_context s)).contexts ≠ []
Proof
  rw[get_current_context_def, return_def, fail_def]
QED

Theorem set_current_context_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (set_current_context c s)).contexts ≠ []
Proof
  rw[set_current_context_def, return_def, fail_def]
QED

(* Layer 3: Monad composition *)

Theorem bind_preserves_nonempty_contexts:
  (∀s. s.contexts ≠ [] ⇒ (SND (g s)).contexts ≠ []) ∧
  (∀x s. s.contexts ≠ [] ⇒ (SND (f x s)).contexts ≠ [])
  ⇒
  s.contexts ≠ [] ⇒ (SND (bind g f s)).contexts ≠ []
Proof
  strip_tac \\ strip_tac \\ simp[bind_def] \\ CASE_TAC \\ Cases_on `q`
  >- (
    simp[]
    \\ `r.contexts ≠ []` by (first_x_assum (qspec_then `s` mp_tac) \\ simp[])
    \\ first_x_assum drule \\ simp[])
  >- (simp[] \\ first_x_assum (qspec_then `s` mp_tac) \\ simp[])
QED

Theorem this_bind_preserves_nonempty_contexts:
  ((SND (g s)).contexts ≠ []) ∧
  (∀x s. s.contexts ≠ [] ⇒ (SND (f x s)).contexts ≠ [])
  ⇒
  (SND (bind g f s)).contexts ≠ []
Proof
  strip_tac \\ simp[bind_def] \\ CASE_TAC \\ CASE_TAC \\ gvs[]
QED

Theorem ignore_bind_preserves_nonempty_contexts:
  (∀s. s.contexts ≠ [] ⇒ (SND (g s)).contexts ≠ []) ∧
  (∀s. s.contexts ≠ [] ⇒ (SND (f s)).contexts ≠ [])
  ⇒
  s.contexts ≠ [] ⇒ (SND (ignore_bind g f s)).contexts ≠ []
Proof
  rw[ignore_bind_def]
  \\ irule bind_preserves_nonempty_contexts \\ rw[]
QED

(* Tactic for proving preservation through monadic composition *)
val preserves_nonempty_tac = rpt (
  (irule bind_preserves_nonempty_contexts \\ rw[]) ORELSE
  (irule ignore_bind_preserves_nonempty_contexts \\ rw[])
)

(* Extended tactic for step_call: also handles option case and uncurry *)
val option_case_preserves = prove(
  ``(s.contexts <> [] ==> (SND (f1 s)).contexts <> []) /\
    (!x. s.contexts <> [] ==> (SND (f2 x s)).contexts <> [])
    ==>
    s.contexts <> [] ==>
    (SND ((case opt of NONE => f1 | SOME x => f2 x) s)).contexts <> []``,
  Cases_on `opt` \\ rw[])

val extended_preserves_tac = rpt (
  (irule bind_preserves_nonempty_contexts \\ rw[]) ORELSE
  (irule ignore_bind_preserves_nonempty_contexts \\ rw[]) ORELSE
  (irule option_case_preserves \\ rw[])
)

(* Layer 4: Higher-level operations *)

Theorem get_gas_left_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (get_gas_left s)).contexts ≠ []
Proof
  rw[get_gas_left_def] \\ preserves_nonempty_tac
QED

Theorem consume_gas_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (consume_gas n s)).contexts ≠ []
Proof
  rw[consume_gas_def] \\ preserves_nonempty_tac
QED

Theorem set_return_data_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (set_return_data rd s)).contexts ≠ []
Proof
  rw[set_return_data_def] \\ preserves_nonempty_tac
QED

Theorem get_num_contexts_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (get_num_contexts s)).contexts ≠ []
Proof
  rw[get_num_contexts_def, return_def]
QED

Theorem reraise_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (reraise e s)).contexts ≠ []
Proof
  rw[reraise_def]
QED

Theorem get_return_data_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (get_return_data s)).contexts ≠ []
Proof
  rw[get_return_data_def] \\ preserves_nonempty_tac
QED

Theorem get_output_to_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (get_output_to s)).contexts ≠ []
Proof
  rw[get_output_to_def] \\ preserves_nonempty_tac
QED

Theorem inc_pc_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (inc_pc s)).contexts ≠ []
Proof
  rw[inc_pc_def] \\ preserves_nonempty_tac
QED

Theorem push_stack_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (push_stack w s)).contexts ≠ []
Proof
  rw[push_stack_def] \\ preserves_nonempty_tac
QED

Theorem write_memory_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (write_memory off data s)).contexts ≠ []
Proof
  rw[write_memory_def] \\ preserves_nonempty_tac
QED

Theorem update_accounts_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (update_accounts f s)).contexts ≠ []
Proof
  rw[update_accounts_def, return_def]
QED

Theorem finish_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (finish s)).contexts ≠ []
Proof
  rw[finish_def]
QED

Theorem revert_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (revert s)).contexts ≠ []
Proof
  rw[revert_def]
QED

Theorem handle_create_preserves_nonempty_contexts[simp]:
  st.contexts ≠ [] ⇒ (SND (handle_create e st)).contexts ≠ []
Proof
  rw[handle_create_def]
  \\ simp[Once bind_def, get_return_data_def, get_current_context_def,
          return_def, fail_def]
  \\ simp[bind_def, get_current_context_def, return_def, fail_def]
  \\ simp[get_output_to_def, bind_def, get_current_context_def,
          return_def, fail_def]
  \\ Cases_on `(FST (HD st.contexts)).msgParams.outputTo`
  >- simp[reraise_def]
  \\ simp[]
  \\ Cases_on `e`
  >- (
    simp[]
    \\ simp[ignore_bind_def, bind_def, assert_def, consume_gas_def,
            update_accounts_def, reraise_def, get_current_context_def,
            set_current_context_def, return_def, fail_def]
    \\ rpt CASE_TAC \\ simp[] )
  \\ simp[reraise_def]
QED

Theorem push_context_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (push_context cr s)).contexts ≠ []
Proof
  rw[push_context_def, return_def]
QED

Theorem inc_pc_or_jump_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (inc_pc_or_jump op s)).contexts ≠ []
Proof
  rw[inc_pc_or_jump_def, bind_def, ignore_bind_def, get_current_context_def,
     set_current_context_def, return_def, fail_def, assert_def]
  \\ rpt CASE_TAC
  \\ simp[set_current_context_def, return_def, bind_def, ignore_bind_def,
          assert_def, fail_def]
  \\ rpt CASE_TAC \\ simp[]
QED

Theorem pop_stack_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (pop_stack n s)).contexts ≠ []
Proof
  rw[pop_stack_def] \\ preserves_nonempty_tac
QED

(* Helper functions for step_* operations *)

Theorem get_tx_params_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (get_tx_params s)).contexts ≠ []
Proof
  rw[get_tx_params_def, return_def]
QED

Theorem get_accounts_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (get_accounts s)).contexts ≠ []
Proof
  rw[get_accounts_def] \\ preserves_nonempty_tac
QED

Theorem get_tStorage_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (get_tStorage s)).contexts ≠ []
Proof
  rw[get_tStorage_def] \\ preserves_nonempty_tac
QED

Theorem set_tStorage_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (set_tStorage x s)).contexts ≠ []
Proof
  rw[set_tStorage_def, return_def]
QED

Theorem get_rollback_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (get_rollback s)).contexts ≠ []
Proof
  rw[get_rollback_def, return_def]
QED

Theorem get_original_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (get_original s)).contexts ≠ []
Proof
  rw[get_original_def, return_def]
QED

Theorem set_original_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (set_original a s)).contexts ≠ []
Proof
  rw[set_original_def, return_def, set_last_accounts_def]
QED

Theorem get_callee_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (get_callee s)).contexts ≠ []
Proof
  rw[get_callee_def] \\ preserves_nonempty_tac
QED

Theorem get_caller_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (get_caller s)).contexts ≠ []
Proof
  rw[get_caller_def] \\ preserves_nonempty_tac
QED

Theorem get_value_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (get_value s)).contexts ≠ []
Proof
  rw[get_value_def] \\ preserves_nonempty_tac
QED

Theorem get_static_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (get_static s)).contexts ≠ []
Proof
  rw[get_static_def] \\ preserves_nonempty_tac
QED

Theorem get_code_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (get_code addr s)).contexts ≠ []
Proof
  rw[get_code_def] \\ preserves_nonempty_tac
QED

Theorem get_call_data_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (get_call_data s)).contexts ≠ []
Proof
  rw[get_call_data_def] \\ preserves_nonempty_tac
QED

Theorem get_current_code_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (get_current_code s)).contexts ≠ []
Proof
  rw[get_current_code_def] \\ preserves_nonempty_tac
QED

Theorem get_return_data_check_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (get_return_data_check off sz s)).contexts ≠ []
Proof
  rw[get_return_data_check_def] \\ preserves_nonempty_tac
QED

Theorem set_jump_dest_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (set_jump_dest d s)).contexts ≠ []
Proof
  rw[set_jump_dest_def] \\ preserves_nonempty_tac
QED

Theorem push_logs_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (push_logs ls s)).contexts ≠ []
Proof
  rw[push_logs_def] \\ preserves_nonempty_tac
QED

Theorem update_gas_refund_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (update_gas_refund r s)).contexts ≠ []
Proof
  Cases_on `r` \\ rw[update_gas_refund_def] \\ preserves_nonempty_tac
QED

Theorem unuse_gas_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (unuse_gas n s)).contexts ≠ []
Proof
  rw[unuse_gas_def] \\ preserves_nonempty_tac
QED

Theorem abort_unuse_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (abort_unuse n s)).contexts ≠ []
Proof
  rw[abort_unuse_def] \\ preserves_nonempty_tac
QED

Theorem abort_create_exists_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (abort_create_exists a s)).contexts ≠ []
Proof
  rw[abort_create_exists_def] \\ preserves_nonempty_tac
QED

Theorem proceed_create_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (proceed_create a b c d e s)).contexts ≠ []
Proof
  rw[proceed_create_def] \\ preserves_nonempty_tac
QED

Theorem abort_call_value_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (abort_call_value n s)).contexts ≠ []
Proof
  rw[abort_call_value_def] \\ preserves_nonempty_tac
QED

Theorem precompile_ecrecover_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (precompile_ecrecover s)).contexts ≠ []
Proof
  rw[precompile_ecrecover_def]
  \\ preserves_nonempty_tac
  \\ Cases_on `ecrecover (word_of_bytes T 0w (take_pad_0 32 x))
               (num_of_be_bytes (take_pad_0 32 (DROP 32 x)))
               (num_of_be_bytes (take_pad_0 32 (DROP 64 x)))
               (num_of_be_bytes (take_pad_0 32 (DROP 96 x)))`
  \\ rw[] \\ preserves_nonempty_tac
QED

Theorem precompile_sha2_256_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (precompile_sha2_256 s)).contexts ≠ []
Proof
  rw[precompile_sha2_256_def]
  \\ preserves_nonempty_tac
  \\ CASE_TAC \\ rw[fail_def] \\ preserves_nonempty_tac
QED

Theorem precompile_ripemd_160_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (precompile_ripemd_160 s)).contexts ≠ []
Proof
  rw[precompile_ripemd_160_def]
  \\ preserves_nonempty_tac
  \\ CASE_TAC \\ rw[fail_def] \\ preserves_nonempty_tac
QED

Theorem precompile_identity_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (precompile_identity s)).contexts ≠ []
Proof
  rw[precompile_identity_def] \\ preserves_nonempty_tac
QED

Theorem precompile_modexp_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (precompile_modexp s)).contexts ≠ []
Proof
  rw[precompile_modexp_def] \\ preserves_nonempty_tac
QED

Theorem precompile_ecadd_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (precompile_ecadd s)).contexts ≠ []
Proof
  rw[precompile_ecadd_def]
  \\ preserves_nonempty_tac
  \\ CASE_TAC \\ rw[fail_def]
  \\ Cases_on `x'` \\ rw[] \\ preserves_nonempty_tac
QED

Theorem precompile_ecmul_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (precompile_ecmul s)).contexts ≠ []
Proof
  rw[precompile_ecmul_def]
  \\ preserves_nonempty_tac
  \\ CASE_TAC \\ rw[fail_def]
  \\ Cases_on `x'` \\ rw[] \\ preserves_nonempty_tac
QED

Theorem precompile_ecpairing_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (precompile_ecpairing s)).contexts ≠ []
Proof
  rw[precompile_ecpairing_def]
  \\ preserves_nonempty_tac
  \\ CASE_TAC \\ rw[fail_def] \\ preserves_nonempty_tac
QED

Theorem precompile_blake2f_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (precompile_blake2f s)).contexts ≠ []
Proof
  rw[precompile_blake2f_def]
  \\ preserves_nonempty_tac
  \\ rw[fail_def] \\ preserves_nonempty_tac
QED

Theorem precompile_point_eval_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (precompile_point_eval s)).contexts ≠ []
Proof
  rw[precompile_point_eval_def]
  \\ preserves_nonempty_tac
  \\ rpt CASE_TAC \\ rw[fail_def] \\ preserves_nonempty_tac
QED

Theorem precompile_bls_g1add_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (precompile_bls_g1add s)).contexts ≠ []
Proof
  rw[precompile_bls_g1add_def]
  \\ preserves_nonempty_tac
  \\ CASE_TAC \\ rw[fail_def] \\ preserves_nonempty_tac
QED

Theorem precompile_bls_g1msm_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (precompile_bls_g1msm s)).contexts ≠ []
Proof
  rw[precompile_bls_g1msm_def]
  \\ preserves_nonempty_tac
  \\ CASE_TAC \\ rw[fail_def] \\ preserves_nonempty_tac
QED

Theorem precompile_bls_g2add_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (precompile_bls_g2add s)).contexts ≠ []
Proof
  rw[precompile_bls_g2add_def]
  \\ preserves_nonempty_tac
  \\ CASE_TAC \\ rw[fail_def] \\ preserves_nonempty_tac
QED

Theorem precompile_bls_g2msm_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (precompile_bls_g2msm s)).contexts ≠ []
Proof
  rw[precompile_bls_g2msm_def]
  \\ preserves_nonempty_tac
  \\ CASE_TAC \\ rw[fail_def] \\ preserves_nonempty_tac
QED

Theorem precompile_bls_pairing_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (precompile_bls_pairing s)).contexts ≠ []
Proof
  rw[precompile_bls_pairing_def]
  \\ preserves_nonempty_tac
  \\ CASE_TAC \\ rw[fail_def] \\ preserves_nonempty_tac
QED

Theorem precompile_bls_map_fp_to_g1_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (precompile_bls_map_fp_to_g1 s)).contexts ≠ []
Proof
  rw[precompile_bls_map_fp_to_g1_def]
  \\ preserves_nonempty_tac
  \\ CASE_TAC \\ rw[fail_def] \\ preserves_nonempty_tac
QED

Theorem precompile_bls_map_fp2_to_g2_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (precompile_bls_map_fp2_to_g2 s)).contexts ≠ []
Proof
  rw[precompile_bls_map_fp2_to_g2_def]
  \\ preserves_nonempty_tac
  \\ CASE_TAC \\ rw[fail_def] \\ preserves_nonempty_tac
QED

Theorem dispatch_precompiles_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (dispatch_precompiles a s)).contexts ≠ []
Proof
  rw[dispatch_precompiles_def, fail_def]
QED

Theorem read_memory_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (read_memory off sz s)).contexts ≠ []
Proof
  rw[read_memory_def] \\ preserves_nonempty_tac
QED

Theorem proceed_call_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (proceed_call a b c d e f g h i s)).contexts ≠ []
Proof
  rw[proceed_call_def] \\ preserves_nonempty_tac
QED

Theorem add_to_delete_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (add_to_delete addr s)).contexts ≠ []
Proof
  rw[add_to_delete_def] \\ preserves_nonempty_tac
QED

Theorem set_domain_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (set_domain d s)).contexts ≠ []
Proof
  rw[set_domain_def, return_def]
QED

Theorem domain_check_preserves_nonempty_contexts[simp]:
  (∀s. s.contexts ≠ [] ⇒ (SND (cont s)).contexts ≠ []) ⇒
  s.contexts ≠ [] ⇒ (SND (domain_check err chk upd cont s)).contexts ≠ []
Proof
  rw[domain_check_def]
  \\ Cases_on `s.msdomain` \\ rw[]
  \\ rw[ignore_bind_def, bind_def, set_domain_def, return_def, fail_def]
QED

Theorem access_address_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (access_address addr s)).contexts ≠ []
Proof
  rw[access_address_def]
  \\ irule domain_check_preserves_nonempty_contexts
  \\ rw[return_def]
QED

Theorem access_slot_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (access_slot sk s)).contexts ≠ []
Proof
  rw[access_slot_def]
  \\ irule domain_check_preserves_nonempty_contexts
  \\ rw[return_def]
QED

Theorem ensure_storage_in_domain_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (ensure_storage_in_domain a s)).contexts ≠ []
Proof
  rw[ensure_storage_in_domain_def]
  \\ irule domain_check_preserves_nonempty_contexts
  \\ rw[return_def]
QED

Theorem memory_expansion_info_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (memory_expansion_info off sz s)).contexts ≠ []
Proof
  rw[memory_expansion_info_def] \\ preserves_nonempty_tac
QED

Theorem expand_memory_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (expand_memory n s)).contexts ≠ []
Proof
  rw[expand_memory_def] \\ preserves_nonempty_tac
QED

Theorem copy_to_memory_preserves_nonempty_contexts:
  (∀s. s.contexts ≠ [] ⇒ (SND (f s)).contexts ≠ []) ⇒
  s.contexts ≠ [] ⇒ (SND (copy_to_memory g off soff sz (SOME f) s)).contexts ≠ []
Proof
  rw[copy_to_memory_def] \\ preserves_nonempty_tac
QED

Theorem copy_to_memory_NONE_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (copy_to_memory g off soff sz NONE s)).contexts ≠ []
Proof
  rw[copy_to_memory_def]
  \\ Cases_on `max_expansion_range (off,sz) (soff,sz)`
  \\ rw[] \\ preserves_nonempty_tac
QED

Theorem write_storage_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (write_storage addr key val s)).contexts ≠ []
Proof
  rw[write_storage_def] \\ preserves_nonempty_tac
QED

Theorem write_transient_storage_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (write_transient_storage addr key val s)).contexts ≠ []
Proof
  rw[write_transient_storage_def] \\ preserves_nonempty_tac
QED

Theorem assert_not_static_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (assert_not_static s)).contexts ≠ []
Proof
  rw[assert_not_static_def] \\ preserves_nonempty_tac
QED

Theorem step_context_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_context op f s)).contexts ≠ []
Proof
  rw[step_context_def] \\ preserves_nonempty_tac
QED

Theorem step_msgParams_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_msgParams op f s)).contexts ≠ []
Proof
  rw[step_msgParams_def] \\ preserves_nonempty_tac
QED

Theorem step_txParams_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_txParams op f s)).contexts ≠ []
Proof
  rw[step_txParams_def] \\ preserves_nonempty_tac
QED

Theorem step_binop_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_binop op f s)).contexts ≠ []
Proof
  rw[step_binop_def] \\ preserves_nonempty_tac
QED

Theorem step_monop_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_monop op f s)).contexts ≠ []
Proof
  rw[step_monop_def] \\ preserves_nonempty_tac
QED

Theorem step_modop_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_modop op f s)).contexts ≠ []
Proof
  rw[step_modop_def] \\ preserves_nonempty_tac
QED

Theorem step_exp_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_exp s)).contexts ≠ []
Proof
  rw[step_exp_def] \\ preserves_nonempty_tac
QED

Theorem step_keccak256_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_keccak256 s)).contexts ≠ []
Proof
  rw[step_keccak256_def] \\ preserves_nonempty_tac
QED

Theorem step_sload_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_sload b s)).contexts ≠ []
Proof
  rw[step_sload_def] \\ preserves_nonempty_tac
QED

Theorem step_sstore_gas_consumption_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_sstore_gas_consumption a k v s)).contexts ≠ []
Proof
  rw[step_sstore_gas_consumption_def] \\ preserves_nonempty_tac
QED

Theorem step_sstore_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_sstore b s)).contexts ≠ []
Proof
  rw[step_sstore_def] \\ preserves_nonempty_tac
QED

Theorem step_balance_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_balance s)).contexts ≠ []
Proof
  rw[step_balance_def] \\ preserves_nonempty_tac
QED

Theorem step_call_data_load_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_call_data_load s)).contexts ≠ []
Proof
  rw[step_call_data_load_def] \\ preserves_nonempty_tac
QED

Theorem step_copy_to_memory_preserves_nonempty_contexts:
  (∀s. s.contexts ≠ [] ⇒ (SND (f s)).contexts ≠ []) ⇒
  s.contexts ≠ [] ⇒ (SND (step_copy_to_memory op (SOME f) s)).contexts ≠ []
Proof
  rw[step_copy_to_memory_def]
  \\ irule bind_preserves_nonempty_contexts \\ rw[]
  \\ irule copy_to_memory_preserves_nonempty_contexts \\ rw[]
QED

Theorem step_copy_to_memory_NONE_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_copy_to_memory op NONE s)).contexts ≠ []
Proof
  rw[step_copy_to_memory_def] \\ preserves_nonempty_tac
QED

Theorem step_copy_to_memory_get_call_data_preserves[simp]:
  s.contexts ≠ [] ⇒ (SND (step_copy_to_memory op (SOME get_call_data) s)).contexts ≠ []
Proof
  rw[] \\ irule step_copy_to_memory_preserves_nonempty_contexts \\ rw[]
QED

Theorem step_copy_to_memory_get_current_code_preserves[simp]:
  s.contexts ≠ [] ⇒ (SND (step_copy_to_memory op (SOME get_current_code) s)).contexts ≠ []
Proof
  rw[] \\ irule step_copy_to_memory_preserves_nonempty_contexts \\ rw[]
QED

Theorem step_return_data_copy_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_return_data_copy s)).contexts ≠ []
Proof
  rw[step_return_data_copy_def]
  \\ irule bind_preserves_nonempty_contexts \\ rw[]
  \\ irule copy_to_memory_preserves_nonempty_contexts \\ rw[]
QED

Theorem step_ext_code_size_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_ext_code_size s)).contexts ≠ []
Proof
  rw[step_ext_code_size_def] \\ preserves_nonempty_tac
QED

Theorem step_ext_code_copy_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_ext_code_copy s)).contexts ≠ []
Proof
  rw[step_ext_code_copy_def]
  \\ irule bind_preserves_nonempty_contexts \\ rw[]
  \\ irule bind_preserves_nonempty_contexts \\ rw[]
  \\ irule copy_to_memory_preserves_nonempty_contexts \\ rw[]
QED

Theorem step_ext_code_hash_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_ext_code_hash s)).contexts ≠ []
Proof
  rw[step_ext_code_hash_def] \\ preserves_nonempty_tac
QED

Theorem step_block_hash_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_block_hash s)).contexts ≠ []
Proof
  rw[step_block_hash_def] \\ preserves_nonempty_tac
QED

Theorem step_blob_hash_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_blob_hash s)).contexts ≠ []
Proof
  rw[step_blob_hash_def] \\ preserves_nonempty_tac
QED

Theorem step_self_balance_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_self_balance s)).contexts ≠ []
Proof
  rw[step_self_balance_def] \\ preserves_nonempty_tac
QED

Theorem step_mload_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_mload s)).contexts ≠ []
Proof
  rw[step_mload_def] \\ preserves_nonempty_tac
QED

Theorem step_mstore_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_mstore op s)).contexts ≠ []
Proof
  rw[step_mstore_def] \\ preserves_nonempty_tac
QED

Theorem step_jump_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_jump s)).contexts ≠ []
Proof
  rw[step_jump_def] \\ preserves_nonempty_tac
QED

Theorem step_jumpi_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_jumpi s)).contexts ≠ []
Proof
  rw[step_jumpi_def] \\ preserves_nonempty_tac
QED

Theorem step_push_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_push n ws s)).contexts ≠ []
Proof
  rw[step_push_def] \\ preserves_nonempty_tac
QED

Theorem step_pop_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_pop s)).contexts ≠ []
Proof
  rw[step_pop_def] \\ preserves_nonempty_tac
QED

Theorem step_dup_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_dup n s)).contexts ≠ []
Proof
  rw[step_dup_def] \\ preserves_nonempty_tac
QED

Theorem step_swap_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_swap n s)).contexts ≠ []
Proof
  rw[step_swap_def] \\ preserves_nonempty_tac
QED

Theorem step_log_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_log n s)).contexts ≠ []
Proof
  rw[step_log_def] \\ preserves_nonempty_tac
QED

Theorem step_return_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_return b s)).contexts ≠ []
Proof
  rw[step_return_def] \\ preserves_nonempty_tac
QED

Theorem step_invalid_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_invalid s)).contexts ≠ []
Proof
  rw[step_invalid_def] \\ preserves_nonempty_tac
QED

Theorem step_self_destruct_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_self_destruct s)).contexts ≠ []
Proof
  rw[step_self_destruct_def] \\ preserves_nonempty_tac
QED

Theorem step_create_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_create b s)).contexts ≠ []
Proof
  rw[step_create_def] \\ preserves_nonempty_tac
QED

Theorem step_call_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_call op s)).contexts ≠ []
Proof
  rw[step_call_def, pairTheory.UNCURRY]
  \\ rpt (
    extended_preserves_tac
    \\ TRY (rw[pairTheory.UNCURRY] \\ extended_preserves_tac)
    \\ TRY (CASE_TAC \\ rw[return_def] \\ extended_preserves_tac)
  )
QED

(* Helper: handle_exception preserves non-empty contexts.
   Key insight: pop_and_incorporate_context is only called when n > 1,
   so we always have at least 1 context after. *)
Theorem handle_exception_preserves_nonempty_contexts:
  st.contexts ≠ [] ⇒ (SND (handle_exception e st)).contexts ≠ []
Proof
  strip_tac
  \\ simp[handle_exception_def, ignore_bind_def, bind_def,
          get_num_contexts_def, return_def]
  \\ TOP_CASE_TAC
  \\ reverse TOP_CASE_TAC
  >- ( pop_assum(SUBST1_TAC o SYM) \\ rw[] \\ preserves_nonempty_tac )
  \\ sg `LENGTH r.contexts = LENGTH st.contexts`
  >- (
    gvs[bind_def,COND_RATOR,get_gas_left_def,CaseEq"bool",return_def,
        get_current_context_def,consume_gas_def,ignore_bind_def,
        assert_def,set_current_context_def,CaseEq"sum",CaseEq"prod",
        set_return_data_def] \\ drule(CONTRAPOS(SPEC_ALL(iffLR LENGTH_NIL)))
    \\ decide_tac)
  \\ rw[reraise_def] >- ( strip_tac \\ gvs[] )
  \\ rw[Once bind_def] \\ TOP_CASE_TAC
  \\ gvs[get_return_data_def]
  \\ pop_assum mp_tac
  \\ simp[Once bind_def] \\ simp[get_current_context_def]
  \\ IF_CASES_TAC >- gvs[] \\ simp[return_def]
  \\ strip_tac \\ gvs[]
  \\ rw[Once bind_def] \\ TOP_CASE_TAC
  \\ gvs[get_output_to_def]
  \\ pop_assum mp_tac
  \\ simp[Once bind_def] \\ simp[get_current_context_def]
  \\ simp[return_def]
  \\ strip_tac \\ gvs[]
  \\ irule this_bind_preserves_nonempty_contexts
  \\ simp[]
  \\ reverse conj_tac
  >- ( irule pop_and_incorporate_context_preserves \\ gvs[] )
  \\ rw[]
  \\ preserves_nonempty_tac
  \\ TOP_CASE_TAC \\ preserves_nonempty_tac
  \\ TOP_CASE_TAC \\ preserves_nonempty_tac
QED

(* Helper: handle_step preserves non-empty contexts *)
Theorem handle_step_preserves_nonempty_contexts:
  st.contexts ≠ [] ⇒ (SND (handle_step e st)).contexts ≠ []
Proof
  rw[handle_step_def, handle_def, reraise_def]
  \\ rpt CASE_TAC
  \\ gvs[handle_create_preserves_nonempty_contexts,
         handle_exception_preserves_nonempty_contexts]
  >- metis_tac[handle_create_preserves_nonempty_contexts, pairTheory.SND]
  \\ metis_tac[handle_create_preserves_nonempty_contexts,
               handle_exception_preserves_nonempty_contexts, pairTheory.SND]
QED

Theorem step_inst_preserves_nonempty_contexts[simp]:
  s.contexts ≠ [] ⇒ (SND (step_inst op s)).contexts ≠ []
Proof
  Cases_on `op` \\ rw[step_inst_def]
  \\ preserves_nonempty_tac
QED

Theorem step_preserves_nonempty_contexts:
  s.contexts ≠ [] ⇒ (SND (step s)).contexts ≠ []
Proof
  strip_tac \\ simp[step_def, handle_def]
  \\ Cases_on `(do context <- get_current_context;
                  if LENGTH context.msgParams.code ≤ context.pc
                  then step_inst Stop
                  else case FLOOKUP context.msgParams.parsed context.pc of
                         NONE => step_inst Invalid
                       | SOME op => do step_inst op; inc_pc_or_jump op od
                od) s`
  \\ Cases_on `q` \\ simp[]
  >- (
    (* INL case: inner computation succeeded *)
    pop_assum mp_tac
    \\ simp[bind_def, ignore_bind_def, get_current_context_def,
            return_def, fail_def]
    \\ rpt TOP_CASE_TAC
    >- (strip_tac \\ gvs[] \\ `r = SND (step_inst Stop s)` by gvs[PAIR] \\ gvs[])
    >- (strip_tac \\ `r = SND (step_inst Invalid s)` by gvs[PAIR] \\ gvs[])
    >- (strip_tac \\ pop_assum mp_tac \\ simp[bind_def, ignore_bind_def]
        \\ rpt TOP_CASE_TAC \\ strip_tac \\ gvs[]
        \\ `r' = SND (step_inst x s)` by gvs[PAIR]
        \\ `r = SND (inc_pc_or_jump x r')` by gvs[PAIR] \\ gvs[])
  )
  >- (
    (* INR case: inner computation raised exception *)
    irule handle_step_preserves_nonempty_contexts
    \\ pop_assum mp_tac
    \\ simp[bind_def, ignore_bind_def, get_current_context_def,
            return_def, fail_def]
    \\ rpt TOP_CASE_TAC \\ strip_tac \\ gvs[]
    >- (`r = SND (step_inst Stop s)` by gvs[PAIR] \\ gvs[])
    >- (`r = SND (step_inst Invalid s)` by gvs[PAIR] \\ gvs[])
    >- (pop_assum mp_tac \\ simp[bind_def, ignore_bind_def]
        \\ rpt TOP_CASE_TAC \\ strip_tac \\ gvs[]
        >- (`r' = SND (step_inst x s)` by gvs[PAIR]
            \\ `r = SND (inc_pc_or_jump x r')` by gvs[PAIR] \\ gvs[])
        >- (`r = SND (step_inst x s)` by gvs[PAIR] \\ gvs[]))
  )
QED

val owhile_contexts = OWHILE_INV_IND
  |> INST_TYPE [``:α`` |-> ``:(unit + exception option) # execution_state``]
  |> INST [``P:(unit + exception option) # execution_state -> bool`` |->
           ``λ(r:unit + exception option, s:execution_state). s.contexts ≠ []``];

Theorem run_preserves_nonempty_contexts:
  run s = SOME rs ∧ s.contexts ≠ []
  ⇒
  (SND rs).contexts ≠ []
Proof
  strip_tac
  \\ fs[run_def]
  \\ irule (SRULE [FORALL_PROD] owhile_contexts)
  \\ CONV_TAC (DEPTH_CONV BETA_CONV)
  \\ qexistsl_tac [`ISL o FST`, `step o SND`, `INL ()`, `FST rs`, `s`]
  \\ simp[o_THM]
  \\ rpt strip_tac
  \\ drule step_preserves_nonempty_contexts
  \\ Cases_on `step p_2`
  \\ gvs[]
QED

Theorem SND_return[simp]:
  SND (return x s) = s
Proof
  rw[return_def]
QED

Theorem SND_fail[simp]:
  SND (fail x y) = y
Proof
  rw[fail_def]
QED

(* -- *)

Definition preserves_wf_accounts_def:
  preserves_wf_accounts (m: α execution) =
  ∀s. EVERY wf_accounts (all_accounts s) ⇒
      EVERY wf_accounts (all_accounts $ SND (m s))
End

Theorem preserves_wf_accounts_bind:
  (∀x. preserves_wf_accounts (f x)) ∧
  preserves_wf_accounts g
  ⇒
  preserves_wf_accounts (bind g f)
Proof
  rw[preserves_wf_accounts_def, bind_def]
  \\ CASE_TAC \\ gs[]
  \\ CASE_TAC \\ gs[]
  \\ metis_tac[SND]
QED

Theorem preserves_wf_accounts_bind_pred:
  (∀x. p x ⇒ preserves_wf_accounts (f x)) ∧
  (∀s a. EVERY wf_accounts (all_accounts s) ∧ FST (g s) = (INL a) ⇒ p a) ∧
  preserves_wf_accounts g
  ⇒
  preserves_wf_accounts (bind g f)
Proof
  rw[preserves_wf_accounts_def, bind_def]
  \\ CASE_TAC \\ gs[]
  \\ CASE_TAC \\ gs[]
  \\ metis_tac[SND, FST]
QED

Theorem preserves_wf_accounts_ignore_bind:
  preserves_wf_accounts f ∧
  preserves_wf_accounts g
  ⇒
  preserves_wf_accounts (ignore_bind g f)
Proof
  rw[ignore_bind_def]
  \\ irule preserves_wf_accounts_bind
  \\ rw[]
QED

Theorem preserves_wf_accounts_get_current_context[simp]:
  preserves_wf_accounts get_current_context
Proof
  rw[preserves_wf_accounts_def, get_current_context_def]
  \\ rw[return_def, fail_def]
QED

Theorem preserves_wf_accounts_assert[simp]:
  preserves_wf_accounts (assert b e)
Proof
  rw[preserves_wf_accounts_def, assert_def]
QED

Theorem preserves_wf_accounts_set_current_context[simp]:
  preserves_wf_accounts (set_current_context c)
Proof
  rw[preserves_wf_accounts_def, set_current_context_def]
  \\ rw[fail_def, return_def]
  \\ gs[all_accounts_def]
  \\ Cases_on`s.contexts` \\ gs[]
QED

Theorem preserves_wf_accounts_return[simp]:
  preserves_wf_accounts (return x)
Proof
  rw[return_def, preserves_wf_accounts_def]
QED

Theorem preserves_wf_accounts_fail[simp]:
  preserves_wf_accounts (fail x)
Proof
  rw[fail_def, preserves_wf_accounts_def]
QED

val tac =
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]));

Theorem preserves_wf_accounts_pop_stack[simp]:
  preserves_wf_accounts (pop_stack n)
Proof
  rw[pop_stack_def] \\ tac
QED

Theorem preserves_wf_accounts_consume_gas[simp]:
  preserves_wf_accounts (consume_gas n)
Proof
  rw[consume_gas_def] \\ tac
QED

Theorem preserves_wf_accounts_push_stack[simp]:
  preserves_wf_accounts (push_stack n)
Proof
  rw[push_stack_def] \\ tac
QED

Theorem preserves_wf_accounts_step_binop[simp]:
  preserves_wf_accounts (step_binop x y)
Proof
  rw[step_binop_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_modop[simp]:
  preserves_wf_accounts (step_modop x y)
Proof
  rw[step_modop_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_monop[simp]:
  preserves_wf_accounts (step_monop x y)
Proof
  rw[step_monop_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
QED

Theorem preserves_wf_accounts_get_tx_params[simp]:
  preserves_wf_accounts get_tx_params
Proof
  rw[get_tx_params_def, preserves_wf_accounts_def, return_def]
QED

Theorem preserves_wf_accounts_step_txParams[simp]:
  preserves_wf_accounts (step_txParams x y)
Proof
  rw[step_txParams_def]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_context[simp]:
  preserves_wf_accounts (step_context x y)
Proof
  rw[step_context_def]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_msgParams[simp]:
  preserves_wf_accounts (step_msgParams x y)
Proof
  rw[step_msgParams_def]
QED

Theorem preserves_wf_accounts_memory_expansion_info[simp]:
  preserves_wf_accounts (memory_expansion_info c e)
Proof
  rw[memory_expansion_info_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_write_memory[simp]:
  preserves_wf_accounts (write_memory c e)
Proof
  rw[write_memory_def] \\ tac
QED

Theorem preserves_wf_accounts_read_memory[simp]:
  preserves_wf_accounts (read_memory c e)
Proof
  rw[read_memory_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_expand_memory[simp]:
  preserves_wf_accounts (expand_memory c)
Proof
  rw[expand_memory_def] \\ tac
QED

Theorem preserves_wf_accounts_copy_to_memory[simp]:
  (∀f. e = SOME f ⇒ preserves_wf_accounts f) ⇒
  preserves_wf_accounts (copy_to_memory a b c d e)
Proof
  rw[copy_to_memory_def, max_expansion_range_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ TRY(irule preserves_wf_accounts_ignore_bind \\ rw[])
  \\ CASE_TAC \\ gs[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_copy_to_memory[simp]:
  (∀f. y = SOME f ⇒ preserves_wf_accounts f) ⇒
  preserves_wf_accounts (step_copy_to_memory x y)
Proof
  rw[step_copy_to_memory_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_exp[simp]:
  preserves_wf_accounts step_exp
Proof
  rw[step_exp_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_keccak256[simp]:
  preserves_wf_accounts step_keccak256
Proof
  rw[step_keccak256_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_get_accounts[simp]:
  preserves_wf_accounts get_accounts
Proof
  rw[get_accounts_def, preserves_wf_accounts_def, return_def]
QED

Theorem preserves_wf_accounts_access_address[simp]:
  preserves_wf_accounts (access_address a)
Proof
  rw[access_address_def, preserves_wf_accounts_def, return_def, fail_def,
     domain_check_def, bind_def, ignore_bind_def, set_domain_def]
  \\ rw[] \\ TOP_CASE_TAC \\ rw[] \\ gs[all_accounts_def]
QED

Theorem preserves_wf_accounts_access_slot[simp]:
  preserves_wf_accounts (access_slot a)
Proof
  rw[access_slot_def, preserves_wf_accounts_def, return_def, fail_def,
     domain_check_def, bind_def, ignore_bind_def, set_domain_def]
  \\ rw[] \\ TOP_CASE_TAC \\ rw[] \\ gs[all_accounts_def]
QED

Theorem preserves_wf_accounts_step_balance[simp]:
  preserves_wf_accounts step_balance
Proof
  rw[step_balance_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_get_call_data[simp]:
  preserves_wf_accounts get_call_data
Proof
  rw[get_call_data_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_call_data_load[simp]:
  preserves_wf_accounts step_call_data_load
Proof
  rw[step_call_data_load_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_get_code[simp]:
  preserves_wf_accounts (get_code x)
Proof
  rw[get_code_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_get_return_data[simp]:
  preserves_wf_accounts get_return_data
Proof
  rw[get_return_data_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_get_return_data_check[simp]:
  preserves_wf_accounts (get_return_data_check y x)
Proof
  rw[get_return_data_check_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_ext_code_copy[simp]:
  preserves_wf_accounts step_ext_code_copy
Proof
  rw[step_ext_code_copy_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_copy_to_memory
  \\ rw[]
QED

Theorem preserves_wf_accounts_step_ext_code_size[simp]:
  preserves_wf_accounts step_ext_code_size
Proof
  rw[step_ext_code_size_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_ext_code_hash[simp]:
  preserves_wf_accounts step_ext_code_hash
Proof
  rw[step_ext_code_hash_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_return_data_copy[simp]:
  preserves_wf_accounts step_return_data_copy
Proof
  rw[step_return_data_copy_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_copy_to_memory
  \\ rw[]
QED

Theorem preserves_wf_accounts_step_block_hash[simp]:
  preserves_wf_accounts step_block_hash
Proof
  rw[step_block_hash_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_get_callee[simp]:
  preserves_wf_accounts get_callee
Proof
  rw[get_callee_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_self_balance[simp]:
  preserves_wf_accounts step_self_balance
Proof
  rw[step_self_balance_def]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_pop[simp]:
  preserves_wf_accounts step_pop
Proof
  rw[step_pop_def]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_mload[simp]:
  preserves_wf_accounts step_mload
Proof
  rw[step_mload_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_step_mstore[simp]:
  preserves_wf_accounts (step_mstore x)
Proof
  rw[step_mstore_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
QED

Theorem preserves_wf_accounts_get_tStorage[simp]:
  preserves_wf_accounts get_tStorage
Proof
  rw[get_tStorage_def, preserves_wf_accounts_def, return_def]
QED

Theorem preserves_wf_accounts_step_sload[simp]:
  preserves_wf_accounts (step_sload x)
Proof
  rw[step_sload_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_get_rollback[simp]:
  preserves_wf_accounts get_rollback
Proof
  rw[get_rollback_def, preserves_wf_accounts_def, return_def]
QED

Theorem preserves_wf_accounts_bind_get_rollback:
  (∀x. wf_accounts x.accounts ⇒ preserves_wf_accounts (f x))
  ⇒
  preserves_wf_accounts (bind get_rollback f)
Proof
  strip_tac
  \\ irule preserves_wf_accounts_bind_pred
  \\ rw[]
  \\ qexists_tac`λx. wf_accounts x.accounts`
  \\ rw[get_rollback_def, return_def, all_accounts_def]
  \\ gs[]
QED

val tac =
  rpt ((irule preserves_wf_accounts_bind_get_rollback \\ rw[]) ORELSE
       (irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]));

Theorem preserves_wf_accounts_set_jump_dest[simp]:
  preserves_wf_accounts (set_jump_dest x)
Proof
  rw[set_jump_dest_def] >> tac
QED

Theorem preserves_wf_accounts_step_jump[simp]:
  preserves_wf_accounts step_jump
Proof
  rw[step_jump_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_step_jumpi[simp]:
  preserves_wf_accounts step_jumpi
Proof
  rw[step_jumpi_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_step_push[simp]:
  preserves_wf_accounts (step_push x y)
Proof
  rw[step_push_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_step_dup[simp]:
  preserves_wf_accounts (step_dup x)
Proof
  rw[step_dup_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_step_swap[simp]:
  preserves_wf_accounts (step_swap x)
Proof
  rw[step_swap_def] >> tac
QED

Theorem preserves_wf_accounts_push_logs[simp]:
  preserves_wf_accounts (push_logs x)
Proof
  rw[push_logs_def] >> tac
QED

Theorem preserves_wf_accounts_get_static[simp]:
  preserves_wf_accounts get_static
Proof
  rw[get_static_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_assert_not_static[simp]:
  preserves_wf_accounts assert_not_static
Proof
  rw[assert_not_static_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_step_log[simp]:
  preserves_wf_accounts (step_log x)
Proof
  rw[step_log_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_set_tStorage[simp]:
  preserves_wf_accounts (set_tStorage x)
Proof
  rw[set_tStorage_def, preserves_wf_accounts_def, return_def, all_accounts_def]
QED

Theorem preserves_wf_accounts_write_transient_storage[simp]:
  preserves_wf_accounts (write_transient_storage x y z)
Proof
  rw[write_transient_storage_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_write_storage[simp]:
  preserves_wf_accounts (write_storage x y z)
Proof
  rw[write_storage_def] >> tac
  \\ rw[preserves_wf_accounts_def, update_accounts_def, return_def]
  \\ rw[update_account_def, lookup_account_def]
  \\ gs[wf_accounts_def, APPLY_UPDATE_THM, all_accounts_def]
  \\ rw[] \\ gs[wf_account_state_def]
QED

Theorem preserves_wf_accounts_update_gas_refund_def[simp]:
  preserves_wf_accounts (update_gas_refund x)
Proof
  Cases_on`x` >>
  rw[update_gas_refund_def] >>
  tac
QED

Theorem preserves_wf_accounts_get_original[simp]:
  preserves_wf_accounts get_original
Proof
  rw[get_original_def, preserves_wf_accounts_def]
  \\ rw[return_def, fail_def]
QED

Theorem preserves_wf_accounts_get_gas_left[simp]:
  preserves_wf_accounts get_gas_left
Proof
  rw[get_gas_left_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_get_current_code[simp]:
  preserves_wf_accounts get_current_code
Proof
  rw[get_current_code_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_get_num_contexts[simp]:
  preserves_wf_accounts get_num_contexts
Proof
  rw[get_num_contexts_def, preserves_wf_accounts_def, return_def]
QED

Theorem preserves_wf_accounts_get_value[simp]:
  preserves_wf_accounts get_value
Proof
  rw[get_value_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_get_caller[simp]:
  preserves_wf_accounts get_caller
Proof
  rw[get_caller_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_step_sstore_gas_consumption[simp]:
  preserves_wf_accounts (step_sstore_gas_consumption x y z)
Proof
  rw[step_sstore_gas_consumption_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_step_sstore[simp]:
  preserves_wf_accounts (step_sstore x)
Proof
  rw[step_sstore_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_finish[simp]:
  preserves_wf_accounts finish
Proof
  rw[finish_def, preserves_wf_accounts_def]
QED

Theorem preserves_wf_accounts_revert[simp]:
  preserves_wf_accounts revert
Proof
  rw[revert_def, preserves_wf_accounts_def]
QED

Theorem preserves_wf_accounts_set_return_data[simp]:
  preserves_wf_accounts (set_return_data x)
Proof
  rw[set_return_data_def] >> tac
QED

Theorem preserves_wf_accounts_step_return[simp]:
  preserves_wf_accounts (step_return x)
Proof
  rw[step_return_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_step_invalid[simp]:
  preserves_wf_accounts step_invalid
Proof
  rw[step_invalid_def] >>
  rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_add_to_delete[simp]:
  preserves_wf_accounts (add_to_delete x)
Proof
  rw[add_to_delete_def, preserves_wf_accounts_def, return_def, all_accounts_def]
QED

val defs = [bind_def, ignore_bind_def, access_address_def,
        get_callee_def, preserves_wf_accounts_def, pop_stack_def,
        get_current_context_def, assert_def, set_current_context_def,
        assert_not_static_def, add_to_delete_def, finish_def,
        set_return_data_def, get_num_contexts_def, get_rollback_def,
        get_static_def, update_accounts_def, get_gas_left_def,
        domain_check_def, set_domain_def,
        get_original_def, get_accounts_def, consume_gas_def, return_def, fail_def]

Theorem wf_account_state_with_balance[simp]:
  wf_account_state (a with balance updated_by b) = wf_account_state a
Proof
  rw[wf_account_state_def]
QED

Theorem preserves_wf_accounts_step_self_destruct[simp]:
  preserves_wf_accounts step_self_destruct
Proof
  rw[step_self_destruct_def]
  \\ rw defs \\ rw[]
  \\ rw defs \\ rw[]
  \\ rw defs
  \\ gs[wf_accounts_def, update_account_def, transfer_value_def,
        all_accounts_def, lookup_account_def]
  \\ rw[APPLY_UPDATE_THM, lookup_account_def] \\ rw[]
  \\ Cases_on`s.contexts` \\ gs[wf_accounts_def]
  \\ Cases_on`s.msdomain` \\ gs[] \\ rw[]
  \\ rw defs \\ rw[]
  \\ gs[wf_accounts_def, update_account_def, transfer_value_def,
        all_accounts_def, lookup_account_def]
  \\ rw[APPLY_UPDATE_THM, lookup_account_def] \\ rw[]
QED

Theorem preserves_wf_accounts_unuse_gas[simp]:
  preserves_wf_accounts (unuse_gas x)
Proof
  rw[unuse_gas_def] >> tac
QED

Theorem preserves_wf_accounts_inc_pc[simp]:
  preserves_wf_accounts inc_pc
Proof
  rw[inc_pc_def] >> tac
QED

Theorem preserves_wf_accounts_abort_unuse[simp]:
  preserves_wf_accounts (abort_unuse x)
Proof
  rw[abort_unuse_def] >> tac
QED

Theorem preserves_wf_accounts_abort_call_value[simp]:
  preserves_wf_accounts (abort_call_value x)
Proof
  rw[abort_call_value_def] >> tac
QED

Theorem preserves_wf_accounts_push_context[simp]:
  wf_accounts (SND x).accounts ⇒
  preserves_wf_accounts (push_context x)
Proof
  rw[push_context_def, preserves_wf_accounts_def, return_def, all_accounts_def]
QED

Theorem preserves_wf_accounts_update_accounts_transfer_value[simp]:
  preserves_wf_accounts (update_accounts (transfer_value x y z))
Proof
  rw[update_accounts_def, preserves_wf_accounts_def, return_def,
     all_accounts_def]
QED

Theorem preserves_wf_accounts_precompile_ecrecover[simp]:
  preserves_wf_accounts precompile_ecrecover
Proof
  rw[precompile_ecrecover_def]
  \\ tac
  \\ CASE_TAC
  \\ rw[]
  \\ tac
QED

Theorem preserves_wf_accounts_precompile_ecadd[simp]:
  preserves_wf_accounts precompile_ecadd
Proof
  rw[precompile_ecadd_def]
  \\ tac
  \\ CASE_TAC
  \\ rw[]
  \\ CASE_TAC
  \\ tac
QED

Theorem preserves_wf_accounts_precompile_ecmul[simp]:
  preserves_wf_accounts precompile_ecmul
Proof
  rw[precompile_ecmul_def]
  \\ tac
  \\ CASE_TAC
  \\ rw[]
  \\ CASE_TAC
  \\ tac
QED

Theorem preserves_wf_accounts_precompile_ecpairing[simp]:
  preserves_wf_accounts precompile_ecpairing
Proof
  rw[precompile_ecpairing_def] \\ tac
  \\ CASE_TAC \\ rw[]
  \\ tac
QED

Theorem preserves_wf_accounts_precompile_blake2f[simp]:
  preserves_wf_accounts precompile_blake2f
Proof
  rw[precompile_blake2f_def] \\ tac
QED

Theorem preserves_wf_accounts_precompile_modexp[simp]:
  preserves_wf_accounts precompile_modexp
Proof
  rw[precompile_modexp_def]
  \\ rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_precompile_sha2_256[simp]:
  preserves_wf_accounts precompile_sha2_256
Proof
  rw[precompile_sha2_256_def]
  \\ rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_precompile_identity[simp]:
  preserves_wf_accounts precompile_identity
Proof
  rw[precompile_identity_def]
  \\ rpt ((irule preserves_wf_accounts_bind \\ rw[]) ORELSE
       (irule preserves_wf_accounts_ignore_bind \\ rw[]))
QED

Theorem preserves_wf_accounts_precompile_ripemd_160[simp]:
  preserves_wf_accounts precompile_ripemd_160
Proof
  rw[precompile_ripemd_160_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem preserves_wf_accounts_precompile_point_eval[simp]:
  preserves_wf_accounts precompile_point_eval
Proof
  rw[precompile_point_eval_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem preserves_wf_accounts_precompile_bls_g1add[simp]:
  preserves_wf_accounts precompile_bls_g1add
Proof
  rw[precompile_bls_g1add_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem preserves_wf_accounts_precompile_bls_g1msm[simp]:
  preserves_wf_accounts precompile_bls_g1msm
Proof
  rw[precompile_bls_g1msm_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem preserves_wf_accounts_precompile_bls_g2add[simp]:
  preserves_wf_accounts precompile_bls_g2add
Proof
  rw[precompile_bls_g2add_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem preserves_wf_accounts_precompile_bls_g2msm[simp]:
  preserves_wf_accounts precompile_bls_g2msm
Proof
  rw[precompile_bls_g2msm_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem preserves_wf_accounts_precompile_bls_pairing[simp]:
  preserves_wf_accounts precompile_bls_pairing
Proof
  rw[precompile_bls_pairing_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem preserves_wf_accounts_precompile_bls_map_fp_to_g1[simp]:
  preserves_wf_accounts precompile_bls_map_fp_to_g1
Proof
  rw[precompile_bls_map_fp_to_g1_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem preserves_wf_accounts_precompile_bls_map_fp2_to_g2[simp]:
  preserves_wf_accounts precompile_bls_map_fp2_to_g2
Proof
  rw[precompile_bls_map_fp2_to_g2_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem preserves_wf_accounts_dispatch_precompiles[simp]:
  preserves_wf_accounts (dispatch_precompiles x)
Proof
  rw[dispatch_precompiles_def]
QED

Theorem preserves_wf_accounts_step_call[simp]:
  preserves_wf_accounts (step_call x)
Proof
  rw[step_call_def, UNCURRY, get_delegate_def, is_delegation_def] >> tac
  >> rw[proceed_call_def] >> tac
QED

Definition preserves_wf_accounts_pred_def:
  preserves_wf_accounts_pred p m ⇔
  ∀s. p s ∧ EVERY wf_accounts (all_accounts s)
      ⇒ EVERY wf_accounts (all_accounts (SND (m s)))
End

Theorem preserves_wf_accounts_bind_get_accounts:
  (∀x. wf_accounts x ⇒ preserves_wf_accounts (f x))
  ⇒
  preserves_wf_accounts (bind get_accounts f)
Proof
  strip_tac
  \\ irule preserves_wf_accounts_bind_pred
  \\ rw[]
  \\ qexists_tac`wf_accounts`
  \\ rw[get_accounts_def, return_def, all_accounts_def]
  \\ rw[]
QED

Theorem preserves_wf_accounts_pred_bind_get_accounts:
  (∀x. preserves_wf_accounts_pred (λs. x = s.rollback.accounts) (f x))
  ⇒
  preserves_wf_accounts (bind get_accounts f)
Proof
  rw[preserves_wf_accounts_pred_def, preserves_wf_accounts_def, bind_def]
  \\ gs[all_accounts_def, get_accounts_def, return_def]
QED

Theorem preserves_wf_accounts_pred_pred_bind:
   (∀x. preserves_wf_accounts_pred q (f x)) ∧
   (∀s s'. p s ⇒ q (SND (g s))) ∧
   preserves_wf_accounts_pred p g ⇒
   preserves_wf_accounts_pred p (monad_bind g f)
Proof
  rw[preserves_wf_accounts_pred_def, bind_def]
  \\ CASE_TAC \\ gs[] \\ reverse CASE_TAC \\ gs[]
  >- metis_tac[SND]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
QED

Theorem preserves_wf_accounts_imp_pred:
   preserves_wf_accounts g ⇒
   preserves_wf_accounts_pred p g
Proof
  rw[preserves_wf_accounts_pred_def, preserves_wf_accounts_def]
QED

Theorem wf_accounts_increment_nonce:
  wf_accounts a ∧ SUC (a x).nonce < 2 ** 64 ⇒
  wf_accounts (increment_nonce x a)
Proof
  rw[wf_accounts_def, wf_account_state_def, increment_nonce_def]
  \\ gs[update_account_def, lookup_account_def, APPLY_UPDATE_THM]
  \\ rw[] \\ rw[]
QED

Theorem preserves_wf_accounts_pred_proceed_create:
  preserves_wf_accounts_pred (λs.
    SUC (s.rollback.accounts a).nonce < 2 ** 64 ∧
    (s.rollback.accounts b).nonce = 0)
  (proceed_create a b c d e)
Proof
  simp[proceed_create_def]
  \\ simp[ignore_bind_def]
  \\ irule preserves_wf_accounts_pred_pred_bind
  \\ simp[]
  \\ reverse conj_tac
  >- (
    rw[preserves_wf_accounts_pred_def,update_accounts_def]
    \\ gvs[return_def, all_accounts_def]
    \\ rw[increment_nonce_def, lookup_account_def,
          update_account_def, APPLY_UPDATE_THM]
    \\ gvs[wf_accounts_def, APPLY_UPDATE_THM]
    \\ rw[]
    \\ gvs[wf_account_state_def] )
  \\ qexists_tac`λs. SUC (s.rollback.accounts b).nonce < 2 ** 64 ∧
                    (s.rollback.accounts a).nonce < 2 ** 64`
  >> reverse conj_tac
  >- (
    rw[increment_nonce_def, update_account_def,
       update_accounts_def, lookup_account_def, APPLY_UPDATE_THM] )
  \\ rw[preserves_wf_accounts_pred_def, set_original_def, set_last_accounts_def,
        get_original_def, get_rollback_def, update_accounts_def,
        push_context_def, bind_def, return_def]
  \\ rw[fail_def]
  \\ gs[all_accounts_def]
  \\ conj_tac
  >- (
    irule wf_accounts_transfer_value
    \\ irule wf_accounts_increment_nonce
    \\ gs[] )
  \\ rw[EVERY_MAP, EVERY_SNOC, set_last_accounts_def]
  \\ gs[EVERY_MEM, MEM_MAP, PULL_EXISTS]
  >- metis_tac[rich_listTheory.MEM_FRONT, list_CASES]
  \\ irule wf_accounts_update_account
  \\ gs[EVERY_MEM, MEM_MAP, PULL_EXISTS]
  \\ metis_tac[rich_listTheory.LAST_MEM]
QED

Theorem preserves_wf_accounts_pred_mono:
  preserves_wf_accounts_pred p f ∧ (∀s. q s ⇒ p s)
  ⇒
  preserves_wf_accounts_pred q f
Proof
  rw[preserves_wf_accounts_pred_def]
QED

Theorem preserves_wf_accounts_ensure_storage_in_domain[simp]:
  preserves_wf_accounts (ensure_storage_in_domain _)
Proof
  rw[preserves_wf_accounts_def, ensure_storage_in_domain_def, assert_def,
     domain_check_def]
  \\ TOP_CASE_TAC \\ gvs[set_domain_def, bind_def, ignore_bind_def]
  \\ rw[return_def] \\ gs[all_accounts_def]
QED

Theorem preserves_wf_accounts_step_create[simp]:
  preserves_wf_accounts (step_create x)
Proof
  simp[step_create_def]
  \\ qpat_abbrev_tac`b1 = COND _ _ _`
  \\ qpat_abbrev_tac`b2 = COND _ _ _`
  \\ irule preserves_wf_accounts_bind \\ simp[] \\ gen_tac
  \\ irule preserves_wf_accounts_bind \\ simp[] \\ gen_tac
  \\ qpat_abbrev_tac`b3 = COND _ _ _`
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ simp[] \\ gen_tac
  \\ irule preserves_wf_accounts_bind \\ simp[] \\ gen_tac
  \\ irule preserves_wf_accounts_pred_bind_get_accounts
  \\ qx_gen_tac`accounts` \\ simp[]
  \\ simp[ignore_bind_def]
  \\ irule preserves_wf_accounts_pred_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- ( irule preserves_wf_accounts_imp_pred \\ rw[] )
  \\ qexists_tac`λs. accounts = s.rollback.accounts`
  \\ reverse conj_tac
  >- rw[assert_def]
  \\ irule preserves_wf_accounts_pred_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- ( irule preserves_wf_accounts_imp_pred \\ rw[] )
  \\ qexists_tac`λs. accounts = s.rollback.accounts`
  \\ reverse conj_tac
  >- (
    rw[access_address_def, return_def, fail_def, domain_check_def]
    \\ Cases_on`s.msdomain` \\ gs[]
    \\ rw[set_domain_def, bind_def, ignore_bind_def, return_def] )
  \\ irule preserves_wf_accounts_pred_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- ( irule preserves_wf_accounts_imp_pred \\ rw[] )
  \\ qexists_tac`λs. accounts = s.rollback.accounts`
  \\ reverse conj_tac
  >- rw[get_gas_left_def, return_def, get_current_context_def,
        bind_def, fail_def]
  \\ gen_tac
  \\ irule preserves_wf_accounts_pred_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- ( irule preserves_wf_accounts_imp_pred \\ rw[] )
  \\ qexists_tac`λs. accounts = s.rollback.accounts`
  \\ reverse conj_tac
  >- (
    rw[consume_gas_def, return_def, get_current_context_def, ignore_bind_def,
       bind_def, fail_def, assert_def, set_current_context_def]
    \\ rw[] )
  \\ irule preserves_wf_accounts_pred_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- ( irule preserves_wf_accounts_imp_pred \\ rw[] )
  \\ qexists_tac`λs. accounts = s.rollback.accounts`
  \\ reverse conj_tac
  >- (
    rw[assert_not_static_def, return_def, get_current_context_def, ignore_bind_def,
       bind_def, fail_def, assert_def, set_current_context_def, get_static_def])
  \\ irule preserves_wf_accounts_pred_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- ( irule preserves_wf_accounts_imp_pred \\ rw[] )
  \\ qexists_tac`λs. accounts = s.rollback.accounts`
  \\ reverse conj_tac
  >- (
    rw[set_return_data_def, return_def, get_current_context_def, ignore_bind_def,
       bind_def, fail_def, assert_def, set_current_context_def, get_static_def])
  \\ irule preserves_wf_accounts_pred_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- ( irule preserves_wf_accounts_imp_pred \\ rw[] )
  \\ qexists_tac`λs. accounts = s.rollback.accounts`
  \\ reverse conj_tac
  >- (
    rw[get_num_contexts_def, return_def, get_current_context_def, ignore_bind_def,
       bind_def, fail_def, assert_def, set_current_context_def, get_static_def])
  \\ gen_tac
  \\ irule preserves_wf_accounts_pred_pred_bind \\ simp[]
  \\ reverse conj_tac
  >- ( irule preserves_wf_accounts_imp_pred \\ rw[] )
  \\ qexists_tac`λs. accounts = s.rollback.accounts`
  \\ reverse conj_tac
  >- (
    rw[ensure_storage_in_domain_def, return_def, ignore_bind_def,
       bind_def, fail_def, assert_def, get_static_def, domain_check_def]
    \\ Cases_on`s.msdomain` \\ gs defs \\ rw[])
  \\ IF_CASES_TAC
  >- ( irule preserves_wf_accounts_imp_pred \\ rw[] )
  \\ IF_CASES_TAC
  >- (
    simp[abort_create_exists_def]
    \\ simp[ignore_bind_def]
    \\ irule preserves_wf_accounts_pred_pred_bind \\ simp[]
    \\ reverse conj_tac
    >- (
      rw[preserves_wf_accounts_pred_def, update_accounts_def, return_def]
      \\ gvs[all_accounts_def]
      \\ irule wf_accounts_increment_nonce
      \\ gs[lookup_account_def] )
    \\ qexists_tac`K T` \\ rw[]
    \\ irule preserves_wf_accounts_imp_pred
    \\ tac )
  \\ gs[account_already_created_def]
  \\ irule preserves_wf_accounts_pred_mono
  \\ irule_at Any preserves_wf_accounts_pred_proceed_create
  \\ simp[]
  \\ gen_tac \\ strip_tac
  \\ gvs[lookup_account_def]
QED

Theorem preserves_wf_accounts_step_blob_hash[simp]:
  preserves_wf_accounts step_blob_hash
Proof
  rw[step_blob_hash_def] \\ tac
QED

Theorem preserves_wf_accounts_step_inst[simp]:
  preserves_wf_accounts (step_inst op)
Proof
  Cases_on`op` \\ rw[step_inst_def]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
QED

Theorem preserves_wf_accounts_handle:
  preserves_wf_accounts f ∧
  (∀e. preserves_wf_accounts (g e))
  ⇒
  preserves_wf_accounts (handle f g)
Proof
  rw[handle_def, preserves_wf_accounts_def]
  \\ CASE_TAC \\ gs[]
  \\ CASE_TAC \\ gs[]
  \\ metis_tac[SND]
QED

Theorem preserves_wf_accounts_get_output_to[simp]:
  preserves_wf_accounts get_output_to
Proof
  rw[get_output_to_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
QED

Theorem preserves_wf_accounts_pop_and_incorporate_context[simp]:
  preserves_wf_accounts (pop_and_incorporate_context x)
Proof
  rw[pop_and_incorporate_context_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ rw[bind_def, ignore_bind_def, pop_context_def, unuse_gas_def,
        preserves_wf_accounts_def, fail_def, return_def, assert_def,
        get_current_context_def, set_current_context_def, update_gas_refund_def,
        push_logs_def]
  \\ rw[] \\ rw[]
  \\ rw[get_current_context_def, set_current_context_def, bind_def,
        ignore_bind_def, return_def, fail_def]
  \\ gs[all_accounts_def]
  \\ Cases_on`s.contexts` \\ gs[set_rollback_def, return_def]
  \\ Cases_on`t` \\ gs[]
QED

Theorem preserves_wf_accounts_reraise[simp]:
  preserves_wf_accounts (reraise e)
Proof
  rw[reraise_def, preserves_wf_accounts_def]
QED

Theorem preserves_wf_accounts_step[simp]:
  preserves_wf_accounts step
Proof
  rw[step_def]
  \\ irule preserves_wf_accounts_handle
  \\ reverse conj_tac
  >- (
    irule preserves_wf_accounts_bind \\ rw[]
    \\ CASE_TAC \\ rw[]
    \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
    \\ rw[inc_pc_or_jump_def]
    \\ irule preserves_wf_accounts_bind \\ rw[]
    \\ CASE_TAC \\ rw[]
    \\ irule preserves_wf_accounts_ignore_bind \\ rw[] )
  \\ rw[handle_step_def]
  \\ irule preserves_wf_accounts_handle
  \\ conj_tac
  >- (
    simp[handle_exception_def] \\ gen_tac
    \\ irule preserves_wf_accounts_ignore_bind
    \\ reverse conj_tac
    >- (
      rw[]
      \\ irule preserves_wf_accounts_bind \\ rw[]
      \\ irule preserves_wf_accounts_ignore_bind \\ rw[] )
    \\ irule preserves_wf_accounts_bind
    \\ rw[]
    \\ irule preserves_wf_accounts_bind \\ rw[]
    \\ irule preserves_wf_accounts_bind \\ rw[]
    \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
    \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
    \\ CASE_TAC \\ rw[] \\ CASE_TAC \\ rw[]
    \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
    \\ irule preserves_wf_accounts_ignore_bind \\ rw[])
  \\ rw[handle_create_def]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ irule preserves_wf_accounts_bind \\ rw[]
  \\ CASE_TAC \\ CASE_TAC \\ CASE_TAC \\ rw[]
  >- (
    tac
    \\ rw[preserves_wf_accounts_def, update_accounts_def, return_def]
    \\ gs[all_accounts_def, update_account_def]
    \\ gs[wf_accounts_def, APPLY_UPDATE_THM] \\ rw[]
    \\ gs[lookup_account_def, wf_account_state_def] )
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ irule preserves_wf_accounts_ignore_bind \\ rw[]
  \\ rw[preserves_wf_accounts_def, assert_def, bind_def, update_accounts_def,
        ignore_bind_def, return_def, reraise_def, max_code_size_def]
  \\ gs[all_accounts_def, update_account_def, lookup_account_def]
  \\ gs[wf_accounts_def, APPLY_UPDATE_THM] \\ rw[]
  \\ gs[wf_account_state_def]
QED

Definition limits_num_contexts_def:
  limits_num_contexts n1 n2 (m: α execution) =
  ∀s. LENGTH s.contexts < n1 ⇒
      LENGTH (SND (m s)).contexts < n2
End

Theorem limits_num_contexts_bind:
  (∀x. limits_num_contexts n2 n3 (f x)) ∧
  limits_num_contexts n1 n2 g ∧
  n2 ≤ n3
  ⇒
  limits_num_contexts n1 n3 (bind g f)
Proof
  rw[limits_num_contexts_def, bind_def]
  \\ CASE_TAC \\ gs[]
  \\ CASE_TAC \\ gs[]
  \\ first_x_assum drule \\ rw[]
QED

Theorem limits_num_contexts_bind_same:
  (∀x. limits_num_contexts n n (f x)) ∧
  limits_num_contexts n n g
  ⇒
  limits_num_contexts n n (bind g f)
Proof
  strip_tac
  \\ irule limits_num_contexts_bind
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
QED

Theorem limits_num_contexts_ignore_bind:
  limits_num_contexts n2 n3 f ∧
  limits_num_contexts n1 n2 g ∧
  n2 ≤ n3
  ⇒
  limits_num_contexts n1 n3 (ignore_bind g f)
Proof
  rw[ignore_bind_def]
  \\ irule limits_num_contexts_bind \\ rw[]
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ rw[]
QED

Theorem limits_num_contexts_ignore_bind_same:
  limits_num_contexts n n f ∧
  limits_num_contexts n n g
  ⇒
  limits_num_contexts n n (ignore_bind g f)
Proof
  strip_tac
  \\ irule limits_num_contexts_ignore_bind
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
QED

Theorem limits_num_contexts_get_current_context[simp]:
  limits_num_contexts n n get_current_context
Proof
  rw[limits_num_contexts_def, get_current_context_def]
  \\ rw[return_def, fail_def]
QED

Theorem limits_num_contexts_assert[simp]:
  limits_num_contexts n n (assert b e)
Proof
  rw[limits_num_contexts_def, assert_def]
QED

Theorem limits_num_contexts_set_current_context[simp]:
  limits_num_contexts n n (set_current_context c)
Proof
  rw[limits_num_contexts_def, set_current_context_def]
  \\ rw[fail_def, return_def]
  \\ gs[all_accounts_def]
  \\ Cases_on`s.contexts` \\ gs[]
QED

Theorem limits_num_contexts_return[simp]:
  limits_num_contexts n n (return x)
Proof
  rw[return_def, limits_num_contexts_def]
QED

Theorem limits_num_contexts_fail[simp]:
  limits_num_contexts n n (fail x)
Proof
  rw[fail_def, limits_num_contexts_def]
QED

val tac = rpt (
  (irule limits_num_contexts_bind_same \\ rw[]) ORELSE
  (irule limits_num_contexts_ignore_bind_same \\ rw[])
)

Theorem limits_num_contexts_pop_stack[simp]:
  limits_num_contexts n n (pop_stack m)
Proof
  rw[pop_stack_def] \\ tac
QED

Theorem limits_num_contexts_consume_gas[simp]:
  limits_num_contexts n n (consume_gas m)
Proof
  rw[consume_gas_def] \\ tac
QED

Theorem limits_num_contexts_push_stack[simp]:
  limits_num_contexts n n (push_stack m)
Proof
  rw[push_stack_def] \\ tac
QED

Theorem limits_num_contexts_step_binop[simp]:
  limits_num_contexts n n (step_binop x y)
Proof
  rw[step_binop_def] \\ tac
QED

Theorem limits_num_contexts_step_modop[simp]:
  limits_num_contexts n n (step_modop x y)
Proof
  rw[step_modop_def] \\ tac
QED

Theorem limits_num_contexts_step_monop[simp]:
  limits_num_contexts n n (step_monop x y)
Proof
  rw[step_monop_def] \\ tac
QED

Theorem limits_num_contexts_get_tx_params[simp]:
  limits_num_contexts n n get_tx_params
Proof
  rw[get_tx_params_def, limits_num_contexts_def, return_def]
QED

Theorem limits_num_contexts_step_txParams[simp]:
  limits_num_contexts n n (step_txParams x y)
Proof
  rw[step_txParams_def] \\ tac
QED

Theorem limits_num_contexts_step_context[simp]:
  limits_num_contexts n n (step_context x y)
Proof
  rw[step_context_def] \\ tac
QED

Theorem limits_num_contexts_step_msgParams[simp]:
  limits_num_contexts n n (step_msgParams x y)
Proof
  rw[step_msgParams_def]
QED

Theorem limits_num_contexts_memory_expansion_info[simp]:
  limits_num_contexts n n (memory_expansion_info c e)
Proof
  rw[memory_expansion_info_def] \\ tac
QED

Theorem limits_num_contexts_write_memory[simp]:
  limits_num_contexts n n (write_memory c e)
Proof
  rw[write_memory_def] \\ tac
QED

Theorem limits_num_contexts_read_memory[simp]:
  limits_num_contexts n n (read_memory c e)
Proof
  rw[read_memory_def] \\ tac
QED

Theorem limits_num_contexts_expand_memory[simp]:
  limits_num_contexts n n (expand_memory c)
Proof
  rw[expand_memory_def] \\ tac
QED

Theorem limits_num_contexts_copy_to_memory[simp]:
  (∀f. e = SOME f ⇒ limits_num_contexts n n f) ⇒
  limits_num_contexts n n (copy_to_memory a b c d e)
Proof
  rw[copy_to_memory_def, max_expansion_range_def]
  \\ irule limits_num_contexts_bind_same \\ rw[]
  \\ irule limits_num_contexts_ignore_bind_same \\ rw[]
  \\ irule limits_num_contexts_bind_same \\ rw[]
  \\ TRY(irule limits_num_contexts_ignore_bind_same \\ rw[])
  \\ CASE_TAC \\ gs[]
  \\ irule limits_num_contexts_bind_same \\ rw[]
  \\ irule limits_num_contexts_ignore_bind_same \\ rw[]
QED

Theorem limits_num_contexts_step_copy_to_memory[simp]:
  (∀f. y = SOME f ⇒ limits_num_contexts n n f) ⇒
  limits_num_contexts n n (step_copy_to_memory x y)
Proof
  rw[step_copy_to_memory_def] \\ tac
QED

Theorem limits_num_contexts_step_exp[simp]:
  limits_num_contexts n n step_exp
Proof
  rw[step_exp_def] \\ tac
QED

Theorem limits_num_contexts_step_keccak256[simp]:
  limits_num_contexts n n step_keccak256
Proof
  rw[step_keccak256_def] \\ tac
QED

Theorem limits_num_contexts_get_accounts[simp]:
  limits_num_contexts n n get_accounts
Proof
  rw[get_accounts_def, limits_num_contexts_def, return_def]
QED

Theorem limits_num_contexts_access_address[simp]:
  limits_num_contexts n n (access_address a)
Proof
  rw[access_address_def, limits_num_contexts_def, return_def, fail_def,
     domain_check_def, ignore_bind_def, bind_def, set_domain_def]
  \\ Cases_on`s.msdomain`
  \\ rw[] \\ gs[all_accounts_def]
QED

Theorem limits_num_contexts_access_slot[simp]:
  limits_num_contexts n n (access_slot a)
Proof
  rw[access_slot_def, limits_num_contexts_def, return_def, fail_def,
     domain_check_def, ignore_bind_def, bind_def, set_domain_def]
  \\ Cases_on`s.msdomain`
  \\ rw[] \\ gs[all_accounts_def]
QED

Theorem limits_num_contexts_step_balance[simp]:
  limits_num_contexts n n step_balance
Proof
  rw[step_balance_def] \\ tac
QED

Theorem limits_num_contexts_get_call_data[simp]:
  limits_num_contexts n n get_call_data
Proof
  rw[get_call_data_def] \\ tac
QED

Theorem limits_num_contexts_step_call_data_load[simp]:
  limits_num_contexts n n step_call_data_load
Proof
  rw[step_call_data_load_def] \\ tac
QED

Theorem limits_num_contexts_get_code[simp]:
  limits_num_contexts n n (get_code x)
Proof
  rw[get_code_def] \\ tac
QED

Theorem limits_num_contexts_get_return_data[simp]:
  limits_num_contexts n n get_return_data
Proof
  rw[get_return_data_def] \\ tac
QED

Theorem limits_num_contexts_get_return_data_check[simp]:
  limits_num_contexts n n (get_return_data_check y x)
Proof
  rw[get_return_data_check_def] \\ tac
QED

Theorem limits_num_contexts_step_ext_code_copy[simp]:
  limits_num_contexts n n step_ext_code_copy
Proof
  rw[step_ext_code_copy_def] \\ tac
QED

Theorem limits_num_contexts_step_ext_code_size[simp]:
  limits_num_contexts n n step_ext_code_size
Proof
  rw[step_ext_code_size_def] \\ tac
QED

Theorem limits_num_contexts_step_ext_code_hash[simp]:
  limits_num_contexts n n step_ext_code_hash
Proof
  rw[step_ext_code_hash_def] \\ tac
QED

Theorem limits_num_contexts_step_return_data_copy[simp]:
  limits_num_contexts n n step_return_data_copy
Proof
  rw[step_return_data_copy_def] \\ tac
QED

Theorem limits_num_contexts_step_block_hash[simp]:
  limits_num_contexts n n step_block_hash
Proof
  rw[step_block_hash_def] \\ tac
QED

Theorem limits_num_contexts_get_callee[simp]:
  limits_num_contexts n n get_callee
Proof
  rw[get_callee_def] \\ tac
QED

Theorem limits_num_contexts_step_self_balance[simp]:
  limits_num_contexts n n step_self_balance
Proof
  rw[step_self_balance_def] \\ tac
QED

Theorem limits_num_contexts_step_pop[simp]:
  limits_num_contexts n n step_pop
Proof
  rw[step_pop_def] \\ tac
QED

Theorem limits_num_contexts_step_mload[simp]:
  limits_num_contexts n n step_mload
Proof
  rw[step_mload_def] \\ tac
QED

Theorem limits_num_contexts_step_mstore[simp]:
  limits_num_contexts n n (step_mstore x)
Proof
  rw[step_mstore_def] \\ tac
QED

Theorem limits_num_contexts_get_tStorage[simp]:
  limits_num_contexts n n get_tStorage
Proof
  rw[get_tStorage_def, limits_num_contexts_def, return_def]
QED

Theorem limits_num_contexts_step_sload[simp]:
  limits_num_contexts n n (step_sload x)
Proof
  rw[step_sload_def] >> tac
QED

Theorem limits_num_contexts_get_rollback[simp]:
  limits_num_contexts n n get_rollback
Proof
  rw[get_rollback_def, limits_num_contexts_def, return_def]
QED

Theorem limits_num_contexts_set_jump_dest[simp]:
  limits_num_contexts n n (set_jump_dest x)
Proof
  rw[set_jump_dest_def] >> tac
QED

Theorem limits_num_contexts_step_jump[simp]:
  limits_num_contexts n n step_jump
Proof
  rw[step_jump_def] >> tac
QED

Theorem limits_num_contexts_step_jumpi[simp]:
  limits_num_contexts n n step_jumpi
Proof
  rw[step_jumpi_def] >> tac
QED

Theorem limits_num_contexts_step_push[simp]:
  limits_num_contexts n n (step_push x y)
Proof
  rw[step_push_def] >> tac
QED

Theorem limits_num_contexts_step_dup[simp]:
  limits_num_contexts n n (step_dup x)
Proof
  rw[step_dup_def] >> tac
QED

Theorem limits_num_contexts_step_swap[simp]:
  limits_num_contexts n n (step_swap x)
Proof
  rw[step_swap_def] >> tac
QED

Theorem limits_num_contexts_push_logs[simp]:
  limits_num_contexts n n (push_logs x)
Proof
  rw[push_logs_def] >> tac
QED

Theorem limits_num_contexts_get_static[simp]:
  limits_num_contexts n n get_static
Proof
  rw[get_static_def] >> tac
QED

Theorem limits_num_contexts_assert_not_static[simp]:
  limits_num_contexts n n assert_not_static
Proof
  rw[assert_not_static_def] >> tac
QED

Theorem limits_num_contexts_step_log[simp]:
  limits_num_contexts n n (step_log x)
Proof
  rw[step_log_def] >> tac
QED

Theorem limits_num_contexts_set_tStorage[simp]:
  limits_num_contexts n n (set_tStorage x)
Proof
  rw[set_tStorage_def, limits_num_contexts_def, return_def, all_accounts_def]
QED

Theorem limits_num_contexts_write_transient_storage[simp]:
  limits_num_contexts n n (write_transient_storage x y z)
Proof
  rw[write_transient_storage_def] >> tac
QED

Theorem limits_num_contexts_write_storage[simp]:
  limits_num_contexts n n (write_storage x y z)
Proof
  rw[write_storage_def] >> tac
  \\ rw[limits_num_contexts_def, update_accounts_def, return_def]
QED

Theorem limits_num_contexts_update_gas_refund_def[simp]:
  limits_num_contexts n n (update_gas_refund x)
Proof
  Cases_on`x` >>
  rw[update_gas_refund_def] >>
  tac
QED

Theorem limits_num_contexts_get_original[simp]:
  limits_num_contexts n n get_original
Proof
  rw[get_original_def, limits_num_contexts_def]
  \\ rw[return_def, fail_def]
QED

Theorem limits_num_contexts_get_gas_left[simp]:
  limits_num_contexts n n get_gas_left
Proof
  rw[get_gas_left_def] >> tac
QED

Theorem limits_num_contexts_get_current_code[simp]:
  limits_num_contexts n n get_current_code
Proof
  rw[get_current_code_def] >> tac
QED

Theorem limits_num_contexts_get_num_contexts[simp]:
  limits_num_contexts n n get_num_contexts
Proof
  rw[get_num_contexts_def, limits_num_contexts_def, return_def]
QED

Theorem limits_num_contexts_get_value[simp]:
  limits_num_contexts n n get_value
Proof
  rw[get_value_def] >> tac
QED

Theorem limits_num_contexts_get_caller[simp]:
  limits_num_contexts n n get_caller
Proof
  rw[get_caller_def] >> tac
QED

Theorem limits_num_contexts_step_sstore_gas_consumption[simp]:
  limits_num_contexts n n (step_sstore_gas_consumption x y z)
Proof
  rw[step_sstore_gas_consumption_def] >> tac
QED

Theorem limits_num_contexts_step_sstore[simp]:
  limits_num_contexts n n (step_sstore x)
Proof
  rw[step_sstore_def] >> tac
QED

Theorem limits_num_contexts_finish[simp]:
  limits_num_contexts n n finish
Proof
  rw[finish_def, limits_num_contexts_def]
QED

Theorem limits_num_contexts_revert[simp]:
  limits_num_contexts n n revert
Proof
  rw[revert_def, limits_num_contexts_def]
QED

Theorem limits_num_contexts_set_return_data[simp]:
  limits_num_contexts n n (set_return_data x)
Proof
  rw[set_return_data_def] >> tac
QED

Theorem limits_num_contexts_step_return[simp]:
  limits_num_contexts n n (step_return x)
Proof
  rw[step_return_def] >> tac
QED

Theorem limits_num_contexts_step_invalid[simp]:
  limits_num_contexts n n step_invalid
Proof
  rw[step_invalid_def] >> tac
QED

Theorem limits_num_contexts_add_to_delete[simp]:
  limits_num_contexts n n (add_to_delete x)
Proof
  rw[add_to_delete_def, limits_num_contexts_def, return_def, all_accounts_def]
QED

Theorem limits_num_contexts_step_self_destruct[simp]:
  limits_num_contexts n n step_self_destruct
Proof
  rw[step_self_destruct_def] \\ tac
  \\ rw[update_accounts_def, limits_num_contexts_def,
        return_def]
QED

Theorem limits_num_contexts_unuse_gas[simp]:
  limits_num_contexts n n (unuse_gas x)
Proof
  rw[unuse_gas_def] >> tac
QED

Theorem limits_num_contexts_inc_pc[simp]:
  limits_num_contexts n n inc_pc
Proof
  rw[inc_pc_def] >> tac
QED

Theorem limits_num_contexts_abort_unuse[simp]:
  limits_num_contexts n n (abort_unuse x)
Proof
  rw[abort_unuse_def] >> tac
QED

Theorem limits_num_contexts_abort_call_value[simp]:
  limits_num_contexts n n (abort_call_value x)
Proof
  rw[abort_call_value_def] >> tac
QED

Theorem limits_num_contexts_push_context[simp]:
  limits_num_contexts n (SUC n) (push_context x)
Proof
  rw[push_context_def, limits_num_contexts_def, return_def, all_accounts_def]
QED

Theorem limits_num_contexts_update_accounts_transfer_value[simp]:
  limits_num_contexts n n (update_accounts (transfer_value x y z))
Proof
  rw[update_accounts_def, limits_num_contexts_def, return_def,
     all_accounts_def]
QED

Theorem limits_num_contexts_precompile_ecrecover[simp]:
  limits_num_contexts n n precompile_ecrecover
Proof
  rw[precompile_ecrecover_def]
  \\ tac
  \\ CASE_TAC
  \\ rw[]
  \\ tac
QED

Theorem limits_num_contexts_precompile_ecadd[simp]:
  limits_num_contexts n n precompile_ecadd
Proof
  rw[precompile_ecadd_def]
  \\ tac
  \\ CASE_TAC
  \\ rw[]
  \\ CASE_TAC
  \\ tac
QED

Theorem limits_num_contexts_precompile_ecmul[simp]:
  limits_num_contexts n n precompile_ecmul
Proof
  rw[precompile_ecmul_def]
  \\ tac
  \\ CASE_TAC
  \\ rw[]
  \\ CASE_TAC
  \\ tac
QED

Theorem limits_num_contexts_precompile_ecpairing[simp]:
  limits_num_contexts n n precompile_ecpairing
Proof
  rw[precompile_ecpairing_def] \\ tac
  \\ CASE_TAC \\ rw[]
  \\ tac
QED

Theorem limits_num_contexts_precompile_blake2f[simp]:
  limits_num_contexts n n precompile_blake2f
Proof
  rw[precompile_blake2f_def] \\ tac
QED

Theorem limits_num_contexts_precompile_modexp[simp]:
  limits_num_contexts n n precompile_modexp
Proof
  rw[precompile_modexp_def] \\ tac
QED

Theorem limits_num_contexts_precompile_sha2_256[simp]:
  limits_num_contexts n n precompile_sha2_256
Proof
  rw[precompile_sha2_256_def] \\ tac
QED

Theorem limits_num_contexts_precompile_identity[simp]:
  limits_num_contexts n n precompile_identity
Proof
  rw[precompile_identity_def] \\ tac
QED

Theorem limits_num_contexts_precompile_ripemd_160[simp]:
  limits_num_contexts n n precompile_ripemd_160
Proof
  rw[precompile_ripemd_160_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem limits_num_contexts_precompile_point_eval[simp]:
  limits_num_contexts n n precompile_point_eval
Proof
  rw[precompile_point_eval_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem limits_num_contexts_precompile_bls_g1add[simp]:
  limits_num_contexts n n precompile_bls_g1add
Proof
  rw[precompile_bls_g1add_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem limits_num_contexts_precompile_bls_g1msm[simp]:
  limits_num_contexts n n precompile_bls_g1msm
Proof
  rw[precompile_bls_g1msm_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem limits_num_contexts_precompile_bls_g2add[simp]:
  limits_num_contexts n n precompile_bls_g2add
Proof
  rw[precompile_bls_g2add_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem limits_num_contexts_precompile_bls_g2msm[simp]:
  limits_num_contexts n n precompile_bls_g2msm
Proof
  rw[precompile_bls_g2msm_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem limits_num_contexts_precompile_bls_pairing[simp]:
  limits_num_contexts n n precompile_bls_pairing
Proof
  rw[precompile_bls_pairing_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem limits_num_contexts_precompile_bls_map_fp_to_g1[simp]:
  limits_num_contexts n n precompile_bls_map_fp_to_g1
Proof
  rw[precompile_bls_map_fp_to_g1_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem limits_num_contexts_precompile_bls_map_fp2_to_g2[simp]:
  limits_num_contexts n n precompile_bls_map_fp2_to_g2
Proof
  rw[precompile_bls_map_fp2_to_g2_def] \\ tac
  \\ CASE_TAC \\ rw[] \\ tac
QED

Theorem limits_num_contexts_dispatch_precompiles[simp]:
  limits_num_contexts n n (dispatch_precompiles x)
Proof
  rw[dispatch_precompiles_def]
QED

Theorem limits_num_contexts_mono:
  limits_num_contexts n1 n2 f ∧ n0 ≤ n1 ∧ n2 ≤ n3 ⇒
  limits_num_contexts n0 n3 f
Proof
  rw[limits_num_contexts_def]
  \\ first_x_assum(qspec_then`s`mp_tac)
  \\ rw[]
QED

Theorem limits_num_contexts_check:
  (n > m ⇒ limits_num_contexts n n2 f) ∧
  (∀n1. n1 ≤ (MIN (PRE n) m) ⇒ limits_num_contexts (SUC n1) n2 g)
  ⇒
  limits_num_contexts n n2 (do
    sd <- get_num_contexts;
    if sd > m then f else g
  od)
Proof
  rw[limits_num_contexts_def, bind_def, ignore_bind_def,
     get_num_contexts_def, return_def, ensure_storage_in_domain_def,
     assert_def]
  \\ rw[] \\ gvs[]
  \\ first_x_assum irule
  \\ Cases_on`n ≤ m` \\ gs[]
  >- (qexists_tac`PRE n` \\ gs[])
  \\ qexists_tac`m` \\ gs[]
QED

Theorem limits_num_contexts_step_call:
  0 < n ∧ n ≤ context_limit + 2 ⇒
  limits_num_contexts n (MIN (SUC n) (context_limit + 2)) (step_call x)
Proof
  strip_tac
  \\ gs[step_call_def, UNCURRY, get_delegate_def, is_delegation_def]
  \\ qpat_abbrev_tac`b1 = COND _ _ _`
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ qpat_abbrev_tac`b2 = COND _ _ _`
  \\ qpat_abbrev_tac`b3 = COND _ _ _`
  \\ qpat_abbrev_tac`b4 = COND _ _ _`
  \\ qpat_abbrev_tac`b5 = COND _ _ _`
  \\ qpat_abbrev_tac`b6 = COND _ _ _`
  \\ irule limits_num_contexts_bind \\ qexists_tac`n`
  \\ reverse conj_tac
  >- (
    rw[]
    \\ CASE_TAC \\ simp[]
    \\ irule limits_num_contexts_bind
    \\ qexists_tac`n` \\ simp[] )
  \\ Cases \\ simp[]
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ simp[Abbr`b6`]
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ simp[]
  \\ reverse conj_tac >- rw[]
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ simp[]
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ rw[]
  >- ( irule limits_num_contexts_mono \\ qexistsl_tac[`n`,`n`] \\ simp[] )
  >- ( irule limits_num_contexts_mono \\ qexistsl_tac[`n`,`n`] \\ simp[] )
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ rw[]
  \\ irule limits_num_contexts_check \\ simp[]
  \\ reverse conj_tac
  >- (
    strip_tac
    \\ irule limits_num_contexts_mono
    \\ qexistsl_tac[`n`,`n`] \\ simp[] )
  \\ gen_tac \\ strip_tac
  \\ simp[proceed_call_def]
  \\ irule limits_num_contexts_bind \\ qexists_tac`SUC n1` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_bind \\ qexists_tac`SUC n1` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`SUC n1` \\ simp[]
  \\ reverse conj_tac >- rw[]
  \\ irule limits_num_contexts_bind \\ qexists_tac`SUC n1` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_bind \\ qexists_tac`SUC n1` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_bind \\ qexists_tac`SUC n1` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_ignore_bind
  \\ qexists_tac`SUC (SUC n1)`
  \\ gs[]
  \\ irule limits_num_contexts_mono
  \\ qexistsl_tac[`n1 + 2`,`n1 + 2`] \\ rw[]
QED

Theorem limits_num_contexts_ensure_storage_in_domain[simp]:
  limits_num_contexts n n (ensure_storage_in_domain _)
Proof
  rw[limits_num_contexts_def, ensure_storage_in_domain_def, assert_def,
     domain_check_def]
  \\ Cases_on`s.msdomain` \\ gs[bind_def, ignore_bind_def, set_domain_def]
  \\ rw[return_def, fail_def]
QED

Theorem limits_num_contexts_reorder_ensure_storage:
  limits_num_contexts x y
  do
    sucDepth <- get_num_contexts;
    ensure_storage_in_domain a;
    f sucDepth
  od ⇔
  limits_num_contexts x y
  do
    ensure_storage_in_domain a;
    sucDepth <- get_num_contexts;
    f sucDepth
  od
Proof
  rw[limits_num_contexts_def, bind_def, ignore_bind_def, get_num_contexts_def,
     ensure_storage_in_domain_def, assert_def, return_def, domain_check_def]
  \\ rw[EQ_IMP_THM] \\ first_x_assum drule
  \\ Cases_on`s.msdomain` \\ gs[fail_def, set_domain_def, return_def]
  \\ rw[]
QED

Theorem limits_num_contexts_set_original[simp]:
  limits_num_contexts n n (set_original a)
Proof
  rw[limits_num_contexts_def, set_original_def]
  \\ rw[return_def, set_last_accounts_def]
  \\ Cases_on`s.contexts` \\ gvs[]
QED

Theorem limits_num_contexts_step_create:
  0 < n ∧ n ≤ context_limit + 2 ⇒
  limits_num_contexts n (MIN (SUC n) (context_limit + 2)) (step_create x)
Proof
  strip_tac
  \\ gs[step_create_def]
  \\ qpat_abbrev_tac`b1 = COND _ _ _`
  \\ qpat_abbrev_tac`b2 = COND _ _ _`
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ qpat_abbrev_tac`b3 = COND _ _ _`
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ simp[]
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ simp[]
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ simp[]
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ simp[]
  \\ irule limits_num_contexts_bind \\ qexists_tac`n` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ simp[]
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ simp[]
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ simp[]
  \\ qpat_abbrev_tac`b4 = COND _ _ _`
  \\ qmatch_goalsub_abbrev_tac`b5 ∨ _`
  \\ Cases_on`b5` \\ gs[]
  >- (
    irule limits_num_contexts_mono \\ qexistsl_tac[`n`,`n`] \\ simp[]
    \\ tac )
  \\ qmatch_goalsub_abbrev_tac`b5 ∨ _`
  \\ Cases_on`b5` \\ gs[]
  >- (
    irule limits_num_contexts_mono \\ qexistsl_tac[`n`,`n`] \\ simp[]
    \\ tac )
  \\ simp[limits_num_contexts_reorder_ensure_storage]
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`n` \\ simp[]
  \\ irule limits_num_contexts_check
  \\ reverse conj_tac
  >- (
    strip_tac
    \\ irule limits_num_contexts_mono
    \\ qexistsl_tac[`n`,`n`] \\ simp[] )
  \\ gen_tac \\ strip_tac
  \\ simp[Abbr`b4`]
  \\ `SUC n1 ≤ n` by gs[]
  \\ `n ≤ MIN (SUC n) 1026` by gs[]
  \\ IF_CASES_TAC
  >- (
    irule limits_num_contexts_mono
    \\ qexistsl_tac[`n`,`n`] \\ simp[]
    \\ rw[abort_create_exists_def]
    \\ tac
    \\ rw[limits_num_contexts_def, update_accounts_def, return_def])
  \\ simp[proceed_create_def]
  \\ qpat_abbrev_tac`b4 = COND _ _ _`
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`SUC n1` \\ simp[]
  \\ reverse conj_tac >- rw[limits_num_contexts_def, update_accounts_def, return_def]
  \\ irule limits_num_contexts_bind \\ qexists_tac`SUC n1` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_bind \\ qexists_tac`SUC n1` \\ simp[] \\ gen_tac
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`SUC n1` \\ simp[]
  \\ irule limits_num_contexts_ignore_bind \\ qexists_tac`SUC n1` \\ simp[]
  \\ reverse conj_tac >- rw[limits_num_contexts_def, update_accounts_def, return_def]
  \\ irule limits_num_contexts_mono
  \\ qexistsl_tac[`SUC n1`,`SUC(SUC n1)`] \\ rw[]
  \\ gs[]
QED

Theorem limits_num_contexts_step_blob_hash[simp]:
  limits_num_contexts n n step_blob_hash
Proof
  rw[step_blob_hash_def] \\ tac
QED

Theorem limits_num_contexts_step_inst:
  n = context_limit + 2 ⇒
  limits_num_contexts n n (step_inst op)
Proof
  Cases_on`op` \\ rw[step_inst_def]
  >- (irule limits_num_contexts_ignore_bind_same \\ rw[])
  \\ `MIN (SUC 1026) (context_limit + 2) = 1026` by rw[]
  \\ `0 < 1026` by rw[]
  \\ `1026 ≤ context_limit + 2` by rw[]
  \\ drule_at Any limits_num_contexts_step_create \\ simp[]
  \\ drule_at Any limits_num_contexts_step_call \\ simp[]
QED

Theorem limits_num_contexts_handle:
  limits_num_contexts n n f ∧
  (∀e. limits_num_contexts n n (g e))
  ⇒
  limits_num_contexts n n (handle f g)
Proof
  rw[handle_def, limits_num_contexts_def]
  \\ CASE_TAC \\ gs[]
  \\ CASE_TAC \\ gs[]
  \\ metis_tac[SND]
QED

Theorem limits_num_contexts_get_output_to[simp]:
  limits_num_contexts n n get_output_to
Proof
  rw[get_output_to_def] \\ tac
QED

Theorem limits_num_contexts_pop_and_incorporate_context[simp]:
  limits_num_contexts n n (pop_and_incorporate_context x)
Proof
  rw[pop_and_incorporate_context_def]
  \\ tac
  \\ rw[bind_def, ignore_bind_def, pop_context_def, unuse_gas_def,
        limits_num_contexts_def, fail_def, return_def, assert_def,
        get_current_context_def, set_current_context_def, update_gas_refund_def,
        push_logs_def, set_rollback_def]
  \\ rw[] \\ rw[]
  \\ Cases_on`s.contexts` \\ gs[]
QED

Theorem limits_num_contexts_reraise[simp]:
  limits_num_contexts n n (reraise e)
Proof
  rw[reraise_def, limits_num_contexts_def]
QED

Theorem limits_num_contexts_step[simp]:
  n = context_limit + 2 ⇒
  limits_num_contexts n n step
Proof
  rw[step_def]
  \\ irule limits_num_contexts_handle
  \\ reverse conj_tac
  >- (
    irule limits_num_contexts_bind_same \\ rw[]
    >- ( irule limits_num_contexts_step_inst \\ rw[] )
    \\ CASE_TAC \\ rw[]
    >- ( irule limits_num_contexts_step_inst \\ rw[] )
    \\ irule limits_num_contexts_ignore_bind_same \\ rw[]
    \\ TRY ( irule limits_num_contexts_step_inst \\ rw[] )
    \\ rw[inc_pc_or_jump_def]
    \\ tac
    \\ CASE_TAC \\ rw[]
    \\ tac)
  \\ rw[handle_step_def]
  \\ irule limits_num_contexts_handle
  \\ conj_tac
  >- (
    simp[handle_exception_def] \\ gen_tac
    \\ irule limits_num_contexts_ignore_bind_same
    \\ reverse conj_tac
    >- ( rw[] \\ tac )
    \\ irule limits_num_contexts_bind_same \\ rw[]
    \\ irule limits_num_contexts_bind_same \\ rw[]
    \\ irule limits_num_contexts_bind_same \\ rw[]
    \\ irule limits_num_contexts_ignore_bind_same \\ rw[]
    \\ irule limits_num_contexts_ignore_bind_same \\ rw[]
    \\ CASE_TAC \\ rw[] \\ CASE_TAC \\ rw[]
    \\ tac )
  \\ rw[handle_create_def]
  \\ tac
  \\ CASE_TAC \\ CASE_TAC \\ CASE_TAC \\ rw[]
  \\ tac
  >- rw[limits_num_contexts_def, update_accounts_def, return_def]
  \\ rw[limits_num_contexts_def, assert_def, bind_def, update_accounts_def,
        ignore_bind_def, return_def, reraise_def]
QED
