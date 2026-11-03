(*
 * Every frame's call data is shorter than 2 ** 256 bytes.
 *
 * The top frame's data is the transaction's, which the 2 ** 24 gas cap and
 * the call data floor cost keep short. A frame pushed by a call gets at
 * most as many bytes as its size operand, a stack word; a frame pushed by
 * a create gets none. A step keeps the other frames' data as it was.
 *)
Theory vfmCalldataBound
Ancestors
  arithmetic list rich_list pair words
  vfmTypes vfmConstants vfmBuffer vfmState vfmContext vfmExecution
  vfmExecutionProp vfmStaticCalls vfmStoragePredicates vfmRunCall
  vfmAccountFrame
Libs
  BasicProvers

Definition calldata_bounded_def:
  calldata_bounded s ⇔
    EVERY (λc. buffer_length c.msgParams.data < 2 ** 256)
      (MAP FST s.contexts)
End

(* -------------------------------------------------------------------------
 * The frame a step pushes.
 * ------------------------------------------------------------------------- *)

Theorem proceed_call_data_length:
  proceed_call op sender address value ao az code gas rd s = (r, s') ∧
  s.contexts ≠ [] ⇒
  buffer_length (FST (HD s'.contexts)).msgParams.data ≤ az
Proof
  strip_tac \\ Cases_on `op ≠ CallCode ∧ 0 < value`
  \\ gvs[proceed_call_def, bind_def, ignore_bind_def,
         get_rollback_def, read_memory_def, get_current_context_def,
         get_caller_def, get_value_def, get_static_def,
         push_context_def, update_accounts_def, return_def, fail_def,
         AllCaseEqs()]
  \\ Cases_on `fIN address precompile_addresses` \\ gvs[return_def]
  \\ TRY (drule (REWRITE_RULE [cp_def] cp_dispatch_precompiles)
          \\ simp[] \\ strip_tac \\ gvs[])
  \\ simp[initial_msg_params_def, buffer_take_to_list, LENGTH_TAKE_EQ]
  \\ rw[]
QED

Theorem proceed_create_data_length:
  proceed_create sender address value code gas s = (r, s') ∧
  s.contexts ≠ [] ⇒
  buffer_length (FST (HD s'.contexts)).msgParams.data = 0
Proof
  strip_tac
  \\ gvs[proceed_create_def, bind_def, ignore_bind_def,
         get_rollback_def, get_original_def, set_original_def,
         update_accounts_def, push_context_def, return_def, fail_def,
         AllCaseEqs()]
  \\ simp[initial_msg_params_def]
QED

Theorem step_push_data_length:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s.contexts < LENGTH s'.contexts ⇒
  buffer_length (FST (HD s'.contexts)).msgParams.data < 2 ** 256
Proof
  strip_tac
  \\ `s.contexts ≠ []` by gvs[wf_state_def]
  \\ drule_all step_grow_dispatch \\ strip_tac
  >- (drule_all step_call_reaches_proceed_call \\ strip_tac
      \\ `u.contexts ≠ []` by gvs[cp_rel_def]
      \\ drule_all proceed_call_data_length \\ decide_tac)
  \\ drule_all step_create_reaches_proceed_create \\ strip_tac
  \\ `u.contexts ≠ []` by gvs[cp_rel_def]
  \\ drule_all proceed_create_data_length \\ simp[]
QED

(* -------------------------------------------------------------------------
 * A step, and the initial state.
 * ------------------------------------------------------------------------- *)

Theorem step_calldata_bounded:
  wf_state s ∧ calldata_bounded s ⇒ calldata_bounded (SND (step s))
Proof
  strip_tac \\ Cases_on `step s` \\ rename1 `step s = (res, s2)` \\ simp[]
  \\ `s.contexts ≠ []` by gvs[wf_state_def]
  \\ Cases_on `LENGTH s2.contexts = LENGTH s.contexts`
  >- (drule_all step_same_frame_foreign \\ strip_tac
      \\ Cases_on `s.contexts` \\ Cases_on `s2.contexts`
      \\ gvs[calldata_bounded_def])
  \\ Cases_on `LENGTH s2.contexts < LENGTH s.contexts`
  >- (drule_all step_pop_foreign \\ strip_tac
      \\ Cases_on `s.contexts` \\ gvs[calldata_bounded_def])
  \\ `LENGTH s.contexts < LENGTH s2.contexts` by decide_tac
  \\ drule_all step_push_data_length \\ strip_tac
  \\ drule_all step_push_foreign \\ strip_tac
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ Cases_on `s2.contexts` \\ gvs[]
  \\ rename1 `s2.contexts = c1 :: rest`
  \\ Cases_on `rest` \\ gvs[calldata_bounded_def]
QED

Theorem LENGTH_le_call_data_tokens:
  ∀data. LENGTH data ≤ call_data_tokens data
Proof
  Induct \\ rw[call_data_tokens_def]
  \\ gvs[call_data_tokens_def]
QED

Theorem initial_state_calldata_bounded:
  initial_state dom static chainId prevHashes blk accs tx = SOME s ⇒
  calldata_bounded s
Proof
  strip_tac \\ gvs[initial_state_def, AllCaseEqs()]
  \\ rpt (pairarg_tac \\ gvs[])
  \\ gvs[apply_intrinsic_cost_def, AllCaseEqs(), calldata_bounded_def,
         initial_msg_params_def]
  \\ gvs[pre_transaction_updates_def, AllCaseEqs()]
  \\ qspec_then `tx.data` assume_tac LENGTH_le_call_data_tokens
  \\ gvs[calldata_floor_cost_def, floor_call_data_cost_def]
  \\ rw[]
QED
