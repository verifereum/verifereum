(*
 * Every frame's call data is shorter than 2 ** 64 bytes, and every frame's
 * gas limit is below 2 ** 64.
 *
 * A call reads the new frame's call data from the caller's memory, so the
 * bound comes from bounding memory. Memory costs gas: memory of length n
 * costs memory_cost n, which is above 2 ** 64 once n reaches 2 ** 64, and
 * no frame uses more gas than its gas limit. The invariant memory_paid
 * says that each frame has used at least the cost of its memory plus the
 * gas the frames above it have not used yet (a call hands that gas over and
 * a return gives back what is left), and that the region a frame returns
 * its output to lies inside its caller's memory, so writing the output
 * does not grow that memory. A new frame's gas limit is at most the gas
 * its caller has used, so it is below the caller's gas limit; the first
 * frame's is at most the transaction's, which is capped at 2 ** 24.
 *
 * The proof follows a step through its operations with a Hoare-style
 * judgement whose precondition carries a credit: gas the current frame has
 * used beyond what memory_paid needs, which a memory expansion or a new
 * frame then spends.
 *)
Theory vfmCalldataBound
Ancestors
  arithmetic list rich_list pair
  vfmTypes vfmConstants vfmBuffer vfmState vfmContext vfmExecution
  vfmExecutionProp vfmPreserves vfmStaticCalls vfmStoragePredicates
  vfmRunCall
Libs
  BasicProvers wordsLib

(* -------------------------------------------------------------------------
 * The invariant.
 * ------------------------------------------------------------------------- *)

(* Each frame has used the cost of its memory plus n plus the gas the
   frames above it have not used. *)
Definition frames_paid_def:
  frames_paid n [] = T ∧
  frames_paid n (c::cs) =
    (memory_cost (buffer_length c.memory) + n ≤ c.gasUsed ∧
     frames_paid (n + (c.msgParams.gasLimit - c.gasUsed)) cs)
End

Definition output_fits_def:
  output_fits (c: context) (caller: context) ⇔
    ∀r. c.msgParams.outputTo = Memory r ∧ 0 < r.size ⇒
        r.offset + r.size ≤ buffer_length caller.memory
End

Definition outputs_fit_def:
  outputs_fit [] = T ∧
  outputs_fit [c] = T ∧
  outputs_fit (c::caller::cs) = (output_fits c caller ∧ outputs_fit (caller::cs))
End

Definition memory_paid_def:
  memory_paid s ⇔
    frames_paid 0 (MAP FST s.contexts) ∧ outputs_fit (MAP FST s.contexts)
End

Definition calldata_bounded_def:
  calldata_bounded s ⇔
    EVERY (λc. buffer_length c.msgParams.data < 2 ** 64 ∧
               c.msgParams.gasLimit < 2 ** 64) (MAP FST s.contexts) ∧
    memory_paid s
End

(* -------------------------------------------------------------------------
 * Memory cost.
 * ------------------------------------------------------------------------- *)

Theorem memory_cost_0[simp]:
  memory_cost 0 = 0
Proof
  EVAL_TAC
QED

Theorem word_size_mono:
  a ≤ b ⇒ word_size a ≤ word_size b
Proof
  rw[word_size_def] \\ irule DIV_LE_MONOTONE \\ simp[]
QED

Theorem memory_cost_mono:
  a ≤ b ⇒ memory_cost a ≤ memory_cost b
Proof
  strip_tac \\ drule word_size_mono \\ strip_tac
  \\ simp_tac std_ss [memory_cost_def, LET_THM]
  \\ irule LESS_EQ_LESS_EQ_MONO \\ conj_tac
  >- (irule DIV_LE_MONOTONE \\ conj_tac >- simp[]
      \\ irule LESS_MONO_MULT2 \\ simp[])
  \\ simp[memory_cost_per_word_def]
QED

Theorem memory_cost_ge_2_64:
  2 ** 64 ≤ byteSize ⇒ 2 ** 64 < memory_cost byteSize
Proof
  strip_tac
  \\ `2 ** 59 ≤ word_size byteSize` by gvs[word_size_def, X_LE_DIV]
  \\ `2 ** 59 * 2 ** 59 ≤ word_size byteSize * word_size byteSize`
       by (irule LESS_MONO_MULT2 \\ simp[])
  \\ `2 ** 118 DIV 512 ≤ word_size byteSize * word_size byteSize DIV 512`
       by (irule DIV_LE_MONOTONE \\ fs[])
  \\ fs[memory_cost_def, memory_cost_per_word_def]
QED

Theorem memory_cost_le_lt_2_64[local]:
  memory_cost n ≤ g ∧ g < 2 ** 64 ⇒ n < 2 ** 64
Proof
  CCONTR_TAC \\ fs[NOT_LESS]
  \\ mp_tac (Q.INST [`byteSize` |-> `n`] memory_cost_ge_2_64) \\ simp[]
QED

Theorem le_word_size_32[local,simp]:
  n ≤ 32 * word_size n
Proof
  rw[word_size_def]
  \\ `(n + 31) MOD 32 < 32` by simp[]
  \\ qspec_then `32` mp_tac DIVISION \\ simp[]
  \\ disch_then (qspec_then `n + 31` mp_tac) \\ simp[]
QED

Theorem ADD_MAX_SUB[local,simp]:
  l + (MAX l n - l) = MAX l n
Proof
  rw[MAX_DEF]
QED

(* -------------------------------------------------------------------------
 * The invariant with a credit, and Hoare triples over it.
 * ------------------------------------------------------------------------- *)

Definition paid_inv_def:
  paid_inv n s ⇔
    s.contexts ≠ [] ∧
    EVERY (λc. buffer_length c.msgParams.data < 2 ** 64 ∧
               c.msgParams.gasLimit < 2 ** 64 ∧
               c.gasUsed ≤ c.msgParams.gasLimit) (MAP FST s.contexts) ∧
    frames_paid n (MAP FST s.contexts) ∧
    outputs_fit (MAP FST s.contexts)
End

Definition paid_at_def:
  paid_at n l s ⇔
    paid_inv n s ∧ buffer_length (FST (HD s.contexts)).memory = l
End

Definition hoare_def:
  hoare P (m: execution_state -> α execution_result) Q ⇔
    ∀s. P s ⇒
      case m s of
      | (INL x, s') => Q x s'
      | (INR e, s') => paid_inv 0 s'
End

Theorem frames_paid_mono:
  ∀cs n m. frames_paid n cs ∧ m ≤ n ⇒ frames_paid m cs
Proof
  Induct \\ rw[frames_paid_def] \\ first_x_assum irule
  \\ qexists_tac `n + (h.msgParams.gasLimit − h.gasUsed)` \\ simp[]
QED

Theorem paid_inv_mono[local]:
  paid_inv n s ∧ m ≤ n ⇒ paid_inv m s
Proof
  rw[paid_inv_def] \\ irule frames_paid_mono \\ first_assum (irule_at Any) \\ simp[]
QED

Theorem paid_at_inv[local]:
  paid_at n l s ⇒ paid_inv 0 s
Proof
  rw[paid_at_def] \\ irule paid_inv_mono \\ first_assum (irule_at Any) \\ simp[]
QED

Theorem paid_inv_HD[local]:
  paid_inv n s ⇒
  s.contexts ≠ [] ∧
  (FST (HD s.contexts)).gasUsed ≤ (FST (HD s.contexts)).msgParams.gasLimit ∧
  (FST (HD s.contexts)).msgParams.gasLimit < 2 ** 64 ∧
  memory_cost (buffer_length (FST (HD s.contexts)).memory) + n ≤
    (FST (HD s.contexts)).gasUsed
Proof
  rw[paid_inv_def] \\ Cases_on `s.contexts` \\ gvs[frames_paid_def]
QED

(* Replacing the current frame by one with the same parameters. *)
Theorem paid_inv_top_update[local]:
  paid_inv n s ∧ s'.contexts ≠ [] ∧ TL s'.contexts = TL s.contexts ∧
  (FST (HD s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams ∧
  (FST (HD s'.contexts)).gasUsed ≤ (FST (HD s'.contexts)).msgParams.gasLimit ∧
  memory_cost (buffer_length (FST (HD s'.contexts)).memory) + n' ≤
    (FST (HD s'.contexts)).gasUsed ∧
  n' + (FST (HD s.contexts)).gasUsed ≤ n + (FST (HD s'.contexts)).gasUsed ⇒
  paid_inv n' s'
Proof
  rw[paid_inv_def]
  \\ Cases_on `s.contexts` \\ Cases_on `s'.contexts` \\ gvs[]
  >- (gvs[frames_paid_def] \\ irule frames_paid_mono
      \\ first_assum (irule_at Any) \\ simp[])
  \\ Cases_on `t` \\ gvs[outputs_fit_def, output_fits_def]
QED

Theorem hoare_bind[local]:
  hoare P g R ∧ (∀x. hoare (R x) (f x) Q) ⇒ hoare P (bind g f) Q
Proof
  rw[hoare_def, bind_def] \\ first_x_assum drule
  \\ Cases_on `g s` \\ Cases_on `q` \\ rw[]
  \\ first_x_assum drule \\ simp[]
QED

Theorem hoare_ignore_bind[local]:
  hoare P g R ∧ (∀x. hoare (R x) f Q) ⇒ hoare P (ignore_bind g f) Q
Proof
  rw[ignore_bind_def] \\ irule hoare_bind \\ qexists_tac `R` \\ simp[]
QED

Theorem hoare_handle[local]:
  hoare P f Q ∧ (∀e. hoare (paid_inv 0) (h e) Q) ⇒ hoare P (handle f h) Q
Proof
  rw[hoare_def, handle_def] \\ first_x_assum drule
  \\ Cases_on `f s` \\ Cases_on `q` \\ rw[]
  \\ first_x_assum drule \\ simp[]
QED

Theorem hoare_paid_inv[local]:
  (∀l. hoare (paid_at n l) m Q) ⇒ hoare (paid_inv n) m Q
Proof
  rw[hoare_def, paid_at_def] \\ first_x_assum irule \\ simp[]
QED

(* -------------------------------------------------------------------------
 * Operations that keep the current frame's memory and parameters, keep the
 * frames below, and do not decrease the gas the current frame has used.
 * ------------------------------------------------------------------------- *)

Definition frame_rel_def:
  frame_rel s s' ⇔
    s.contexts ≠ [] ⇒
      s'.contexts ≠ [] ∧ TL s'.contexts = TL s.contexts ∧
      (FST (HD s'.contexts)).memory = (FST (HD s.contexts)).memory ∧
      (FST (HD s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams ∧
      (FST (HD s.contexts)).gasUsed ≤ (FST (HD s'.contexts)).gasUsed ∧
      ((FST (HD s.contexts)).gasUsed ≤
         (FST (HD s.contexts)).msgParams.gasLimit ⇒
       (FST (HD s'.contexts)).gasUsed ≤
         (FST (HD s'.contexts)).msgParams.gasLimit)
End

Overload plain[local] = “preserves frame_rel”

Theorem frame_rel_refl[local,simp]:
  frame_rel s s
Proof
  rw[frame_rel_def]
QED

Theorem frame_rel_trans[local]:
  frame_rel s1 s2 ∧ frame_rel s2 s3 ⇒ frame_rel s1 s3
Proof
  rw[frame_rel_def] \\ gvs[]
QED

Theorem frame_rel_paid_at[local]:
  frame_rel s s' ∧ paid_at n l s ⇒ paid_at n l s'
Proof
  rw[paid_at_def] \\ imp_res_tac paid_inv_HD \\ gvs[frame_rel_def]
  \\ drule paid_inv_top_update \\ disch_then irule \\ simp[]
QED

Theorem plain_bind[local,simp]:
  plain g ∧ (∀x. plain (f x)) ⇒ plain (bind g f)
Proof
  rw[] \\ irule preserves_bind \\ rw[] \\ metis_tac[frame_rel_trans]
QED

Theorem plain_ignore_bind[local,simp]:
  plain g ∧ plain f ⇒ plain (ignore_bind g f)
Proof
  rw[] \\ irule preserves_ignore_bind \\ rw[] \\ metis_tac[frame_rel_trans]
QED

Theorem plain_cond[local,simp]:
  plain m1 ∧ plain m2 ⇒ plain (if b then m1 else m2)
Proof
  rw[]
QED

Theorem plain_same[local]:
  (∀s. (SND (m s)).contexts = s.contexts) ⇒ plain m
Proof
  rw[preserves_def] \\ first_x_assum (qspec_then `s` mp_tac)
  \\ rw[frame_rel_def]
QED

Theorem plain_domain_check[local]:
  plain cont ⇒ plain (domain_check err check ad cont)
Proof
  rw[preserves_def, domain_check_def]
  \\ gvs[AllCaseEqs(), ignore_bind_def, bind_def, set_domain_def, return_def,
         fail_def]
  \\ first_x_assum drule \\ rw[frame_rel_def]
QED

Theorem plain_basic[local,simp]:
  plain (return x) ∧
  plain (fail e) ∧
  plain (assert b e) ∧
  plain finish ∧
  plain revert ∧
  plain (reraise eo) ∧
  plain get_num_contexts ∧
  plain get_tx_params ∧
  plain get_accounts ∧
  plain (update_accounts f) ∧
  plain get_tStorage ∧
  plain (set_tStorage t) ∧
  plain get_rollback ∧
  plain (set_rollback r) ∧
  plain get_original ∧
  plain (set_original accs) ∧
  plain (add_to_delete a) ∧
  plain (set_domain d)
Proof
  rpt conj_tac \\ irule plain_same
  \\ rw[return_def, fail_def, assert_def, finish_def, revert_def,
        reraise_def, get_num_contexts_def, get_tx_params_def,
        get_accounts_def, update_accounts_def, get_tStorage_def,
        set_tStorage_def, get_rollback_def, set_rollback_def,
        get_original_def, set_original_def, add_to_delete_def,
        set_domain_def]
QED

Theorem plain_access[local,simp]:
  plain (access_address a) ∧
  plain (access_slot x) ∧
  plain (ensure_storage_in_domain a)
Proof
  rw[access_address_def, access_slot_def, ensure_storage_in_domain_def]
  \\ irule plain_domain_check
  \\ irule plain_same \\ rw[return_def]
QED

Theorem plain_get_current_context[local,simp]:
  plain get_current_context
Proof
  irule plain_same \\ rw[get_current_context_def, return_def, fail_def]
QED

Theorem plain_frame_ops[local,simp]:
  plain get_gas_left ∧
  plain get_callee ∧
  plain get_caller ∧
  plain get_value ∧
  plain get_output_to ∧
  plain get_return_data ∧
  plain (get_return_data_check off sz) ∧
  plain get_static ∧
  plain (get_code a) ∧
  plain get_current_code ∧
  plain get_call_data ∧
  plain (read_memory off sz) ∧
  plain (memory_expansion_info off sz) ∧
  plain assert_not_static
Proof
  rw[get_gas_left_def, get_callee_def, get_caller_def, get_value_def,
     get_output_to_def, get_return_data_def, get_return_data_check_def,
     get_static_def, get_code_def, get_current_code_def,
     get_call_data_def, read_memory_def, memory_expansion_info_def,
     assert_not_static_def]
  \\ rpt (FIRST [irule plain_bind, irule plain_ignore_bind] \\ rw[])
QED

Theorem plain_set_ops[local,simp]:
  plain (set_return_data rd) ∧
  plain (set_jump_dest j) ∧
  plain (push_logs ls) ∧
  plain (update_gas_refund ar) ∧
  plain inc_pc
Proof
  PairCases_on `ar`
  \\ rw[preserves_def, set_return_data_def, set_jump_dest_def, push_logs_def,
        update_gas_refund_def, inc_pc_def, bind_def, get_current_context_def,
        set_current_context_def, return_def, fail_def]
  \\ gvs[AllCaseEqs(), frame_rel_def]
QED

Theorem plain_stack_ops[local,simp]:
  plain (pop_stack n) ∧
  plain (push_stack v) ∧
  plain (consume_gas k)
Proof
  rw[preserves_def, pop_stack_def, push_stack_def, consume_gas_def,
     bind_def, ignore_bind_def, get_current_context_def,
     set_current_context_def, assert_def, return_def, fail_def]
  \\ gvs[AllCaseEqs(), frame_rel_def]
QED

(* -------------------------------------------------------------------------
 * Specifications of the operations that change memory or gas, in the form
 * in which they start a sequence.
 * ------------------------------------------------------------------------- *)

Theorem hoare_weaken_at[local]:
  hoare P m (λx. paid_at n l) ⇒ hoare P m (λx. paid_inv 0)
Proof
  rw[hoare_def] \\ first_x_assum drule \\ CASE_TAC \\ CASE_TAC \\ rw[]
  \\ drule paid_at_inv \\ simp[]
QED

Theorem hoare_plain[local]:
  plain g ⇒ hoare (paid_at n l) g (λx. paid_at n l)
Proof
  rw[hoare_def, preserves_def] \\ Cases_on `g s`
  \\ first_x_assum drule \\ strip_tac
  \\ drule_all frame_rel_paid_at \\ strip_tac
  \\ Cases_on `q` \\ simp[] \\ metis_tac[paid_at_inv]
QED

Theorem hb_plain[local]:
  plain g ∧ (∀x. hoare (paid_at n l) (f x) Q) ⇒
  hoare (paid_at n l) (bind g f) Q
Proof
  rw[] \\ irule hoare_bind \\ irule_at Any hoare_plain \\ simp[]
QED

Theorem hib_plain[local]:
  plain g ∧ hoare (paid_at n l) f Q ⇒
  hoare (paid_at n l) (ignore_bind g f) Q
Proof
  rw[] \\ irule hoare_ignore_bind \\ irule_at Any hoare_plain \\ simp[]
QED

Theorem ht_plain[local]:
  plain g ⇒ hoare (paid_at n l) g (λx. paid_inv 0)
Proof
  rw[] \\ drule hoare_plain \\ rw[hoare_def]
  \\ first_x_assum drule \\ CASE_TAC \\ CASE_TAC \\ rw[]
  \\ metis_tac[paid_at_inv]
QED

Theorem hoare_consume_gas[local]:
  hoare (paid_at n l) (consume_gas k) (λx. paid_at (n + k) l)
Proof
  rw[hoare_def, paid_at_def] \\ imp_res_tac paid_inv_HD
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ gvs[consume_gas_def, bind_def, ignore_bind_def, get_current_context_def,
         set_current_context_def, assert_def, return_def, fail_def]
  \\ IF_CASES_TAC \\ gvs[]
  >- (drule paid_inv_top_update \\ disch_then irule \\ simp[])
  \\ irule paid_inv_mono \\ first_assum (irule_at Any) \\ simp[]
QED

Theorem hib_consume[local]:
  hoare (paid_at (n + k) l) f Q ⇒
  hoare (paid_at n l) (ignore_bind (consume_gas k) f) Q
Proof
  rw[] \\ irule hoare_ignore_bind \\ irule_at Any hoare_consume_gas \\ simp[]
QED

Theorem hoare_unuse_gas[local]:
  k ≤ n ⇒ hoare (paid_at n l) (unuse_gas k) (λx. paid_at (n - k) l)
Proof
  rw[hoare_def, paid_at_def] \\ imp_res_tac paid_inv_HD
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ gvs[unuse_gas_def, bind_def, ignore_bind_def, get_current_context_def,
         set_current_context_def, assert_def, return_def, fail_def]
  \\ drule paid_inv_top_update \\ disch_then irule \\ simp[]
QED

Theorem hib_unuse[local]:
  k ≤ n ∧ hoare (paid_at (n - k) l) f Q ⇒
  hoare (paid_at n l) (ignore_bind (unuse_gas k) f) Q
Proof
  rw[] \\ irule hoare_ignore_bind \\ irule_at Any hoare_unuse_gas \\ simp[]
QED

Theorem hb_memory_expansion_info[local]:
  hoare (paid_at n l)
    (f <| cost := memory_expansion_cost l
                    (if 0 < sz then word_size (off + sz) * 32 else 0)
        ; expand_by := MAX l (if 0 < sz then word_size (off + sz) * 32 else 0)
                       - l |>) Q ⇒
  hoare (paid_at n l) (bind (memory_expansion_info off sz) f) Q
Proof
  rw[hoare_def, paid_at_def, memory_expansion_info_def, bind_def,
     get_current_context_def, return_def]
  \\ imp_res_tac paid_inv_HD \\ gvs[]
QED

Theorem hoare_expand_memory[local]:
  memory_expansion_cost l m ≤ n ⇒
  hoare (paid_at n l) (expand_memory (MAX l m - l))
    (λx. paid_at (n - memory_expansion_cost l m) (MAX l m))
Proof
  rw[hoare_def, paid_at_def] \\ imp_res_tac paid_inv_HD
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ gvs[expand_memory_def, bind_def, get_current_context_def,
         set_current_context_def, return_def]
  \\ drule paid_inv_top_update \\ disch_then irule
  \\ gvs[memory_expansion_cost_def]
  \\ `memory_cost (buffer_length (FST h).memory) ≤
      memory_cost (MAX (buffer_length (FST h).memory) m)`
       by (irule memory_cost_mono \\ simp[])
  \\ simp[]
QED

Theorem hib_expand[local]:
  memory_expansion_cost l m ≤ n ∧
  hoare (paid_at (n - memory_expansion_cost l m) (MAX l m)) f Q ⇒
  hoare (paid_at n l) (ignore_bind (expand_memory (MAX l m - l)) f) Q
Proof
  rw[] \\ irule hoare_ignore_bind \\ irule_at Any hoare_expand_memory
  \\ simp[]
QED

Theorem hoare_write_memory[local]:
  bs = [] ∨ off + LENGTH bs ≤ l ⇒
  hoare (paid_at n l) (write_memory off bs) (λx. paid_at n l)
Proof
  strip_tac \\ rw[hoare_def, paid_at_def] \\ imp_res_tac paid_inv_HD
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ gvs[write_memory_def, bind_def, get_current_context_def,
         set_current_context_def, return_def]
  >- gvs[paid_inv_def]
  \\ conj_tac >- (drule paid_inv_top_update \\ disch_then irule \\ rw[MAX_DEF])
  \\ rw[MAX_DEF]
QED

Theorem hib_write[local]:
  (bs = [] ∨ off + LENGTH bs ≤ l) ∧ hoare (paid_at n l) f Q ⇒
  hoare (paid_at n l) (ignore_bind (write_memory off bs) f) Q
Proof
  rw[] \\ irule hoare_ignore_bind \\ irule_at Any hoare_write_memory
  \\ simp[]
QED

Theorem ht_write[local]:
  bs = [] ∨ off + LENGTH bs ≤ l ⇒
  hoare (paid_at n l) (write_memory off bs) (λx. paid_inv 0)
Proof
  disch_then (mp_tac o MATCH_MP hoare_write_memory) \\ rw[hoare_def]
  \\ first_x_assum drule \\ CASE_TAC \\ CASE_TAC \\ rw[]
  \\ metis_tac[paid_at_inv]
QED

Theorem hb_read_memory[local]:
  (∀d. LENGTH d ≤ l ∧ LENGTH d ≤ sz ⇒ hoare (paid_at n l) (f d) Q) ⇒
  hoare (paid_at n l) (bind (read_memory off sz) f) Q
Proof
  rw[hoare_def, paid_at_def, read_memory_def, bind_def,
     get_current_context_def, return_def]
  \\ imp_res_tac paid_inv_HD \\ gvs[]
  \\ first_x_assum irule \\ simp[buffer_take_to_list, LENGTH_TAKE_EQ]
  \\ rw[]
QED

(* A new frame, with no memory and no gas used yet, whose gas limit is
   paid from the credit and whose call data and output region are inside
   the caller's memory. *)
Theorem hoare_push_context[local]:
  c.gasUsed = 0 ∧ buffer_length c.memory = 0 ∧ c.msgParams.gasLimit ≤ n ∧
  buffer_length c.msgParams.data ≤ l ∧
  (∀r. c.msgParams.outputTo = Memory r ∧ 0 < r.size ⇒ r.offset + r.size ≤ l) ⇒
  hoare (paid_at n l) (push_context (c, rb)) (λx. paid_at 0 0)
Proof
  rw[hoare_def, paid_at_def, push_context_def, return_def]
  \\ imp_res_tac paid_inv_HD
  \\ `buffer_length (FST (HD s.contexts)).memory < 2 ** 64`
       by (irule memory_cost_le_lt_2_64
           \\ qexists_tac `(FST (HD s.contexts)).msgParams.gasLimit` \\ gvs[])
  \\ Cases_on `s.contexts` \\ gvs[paid_inv_def, frames_paid_def,
                                  outputs_fit_def, output_fits_def]
  \\ irule frames_paid_mono \\ first_assum (irule_at Any) \\ simp[]
QED

Theorem hib_push_context[local]:
  c.gasUsed = 0 ∧ buffer_length c.memory = 0 ∧ c.msgParams.gasLimit ≤ n ∧
  buffer_length c.msgParams.data ≤ l ∧
  (∀r. c.msgParams.outputTo = Memory r ∧ 0 < r.size ⇒ r.offset + r.size ≤ l) ∧
  hoare (paid_at 0 0) f Q ⇒
  hoare (paid_at n l) (ignore_bind (push_context (c, rb)) f) Q
Proof
  rw[] \\ irule hoare_ignore_bind \\ irule_at Any hoare_push_context
  \\ simp[]
QED

Theorem ht_push_context[local]:
  c.gasUsed = 0 ∧ buffer_length c.memory = 0 ∧ c.msgParams.gasLimit ≤ n ∧
  buffer_length c.msgParams.data ≤ l ∧
  (∀r. c.msgParams.outputTo = Memory r ∧ 0 < r.size ⇒ r.offset + r.size ≤ l) ⇒
  hoare (paid_at n l) (push_context (c, rb)) (λx. paid_inv 0)
Proof
  strip_tac \\ irule hoare_weaken_at \\ qexistsl_tac [`0`, `0`]
  \\ irule hoare_push_context \\ simp[]
QED

(* The tactic that follows a sequence of operations. *)

(* A goal "plain m" must be solved by rewriting, so that the rules for
   plain operations apply only where they lose nothing. *)
fun plain_guard simps (g as (_, w)) =
  let val (f, _) = strip_comb w in
    if is_const f andalso fst (dest_const f) = "preserves"
    then (rw simps \\ NO_TAC) g
    else ALL_TAC g
  end;

fun hoare_step_with ths simps =
  FIRST (map irule ths @
         [irule hb_memory_expansion_info,
          irule hb_read_memory,
          irule hib_consume,
          irule hib_unuse,
          irule hib_expand,
          irule hib_write,
          irule hib_push_context,
          irule ht_push_context,
          irule hb_plain \\ rpt conj_tac \\ plain_guard simps,
          irule hib_plain \\ rpt conj_tac \\ plain_guard simps,
          irule ht_write,
          irule ht_plain \\ plain_guard simps,
          pairarg_tac, CASE_TAC]) \\ rw simps;

fun hoare_tac_with simps = rpt (hoare_step_with [] simps);

val hoare_tac = hoare_tac_with [];

(* At most k steps, for long sequences: each use is one proof step. *)
fun hoare_steps ths k =
  if k = 0 then ALL_TAC
  else (hoare_step_with ths [] \\ hoare_steps ths (k - 1)) ORELSE ALL_TAC;

(* -------------------------------------------------------------------------
 * The operations of a step that keep the current frame's memory.
 * ------------------------------------------------------------------------- *)

Theorem bind_ignore_bind[local,simp]:
  bind (ignore_bind g h) f = ignore_bind g (bind h f)
Proof
  rw[ignore_bind_def]
QED

Theorem plain_case_option[local,simp]:
  plain m_none ∧ (∀x. plain (m_some x)) ⇒
  plain (case opt of NONE => m_none | SOME x => m_some x)
Proof
  Cases_on `opt` \\ rw[]
QED

Theorem plain_case_pair[local,simp]:
  (∀x y. plain (f x y)) ⇒ plain (case p of (x,y) => f x y)
Proof
  Cases_on `p` \\ rw[]
QED

fun plain_tac simps =
  rpt (FIRST [irule plain_bind, irule plain_ignore_bind, CASE_TAC,
              pairarg_tac] \\ rw simps);

Theorem plain_swap_jump[local,simp]:
  plain (step_swap n) ∧ plain (inc_pc_or_jump op)
Proof
  rw[preserves_def, step_swap_def, inc_pc_or_jump_def, consume_gas_def,
     bind_def, ignore_bind_def, get_current_context_def,
     set_current_context_def, assert_def, return_def, fail_def]
  \\ every_case_tac
  \\ gvs[AllCaseEqs(), frame_rel_def, bind_def, ignore_bind_def,
         get_current_context_def, set_current_context_def, assert_def,
         return_def, fail_def]
QED

Theorem plain_steps[local,simp]:
  plain (step_binop op f) ∧
  plain (step_monop op g) ∧
  plain (step_modop op h) ∧
  plain (step_context op i) ∧
  plain (step_msgParams op j) ∧
  plain (step_txParams op k) ∧
  plain step_exp ∧
  plain (step_sload b) ∧
  plain (step_sstore_gas_consumption a key v) ∧
  plain (step_sstore b) ∧
  plain step_balance ∧
  plain step_call_data_load ∧
  plain step_ext_code_size ∧
  plain step_ext_code_hash ∧
  plain step_block_hash ∧
  plain step_blob_hash ∧
  plain step_self_balance ∧
  plain step_jump ∧
  plain step_jumpi ∧
  plain (step_push n ws) ∧
  plain step_pop ∧
  plain (step_dup n) ∧
  plain step_self_destruct
Proof
  rw[step_binop_def, step_monop_def, step_modop_def, step_context_def,
     step_msgParams_def, step_txParams_def, step_exp_def, step_sload_def,
     step_sstore_gas_consumption_def, step_sstore_def, step_balance_def,
     step_call_data_load_def, step_ext_code_size_def,
     step_ext_code_hash_def, step_block_hash_def, step_blob_hash_def,
     step_self_balance_def, step_jump_def, step_jumpi_def, step_push_def,
     step_pop_def, step_dup_def, step_self_destruct_def, write_storage_def,
     write_transient_storage_def]
  \\ plain_tac []
QED

Theorem plain_precompiles[local,simp]:
  plain (dispatch_precompiles a)
Proof
  rw[dispatch_precompiles_def, precompile_ecrecover_def,
     precompile_sha2_256_def, precompile_ripemd_160_def,
     precompile_identity_def, precompile_modexp_def, precompile_ecadd_def,
     precompile_ecmul_def, precompile_ecpairing_def, precompile_blake2f_def,
     precompile_point_eval_def, precompile_bls_g1add_def,
     precompile_bls_g1msm_def, precompile_bls_g2add_def,
     precompile_bls_g2msm_def, precompile_bls_pairing_def,
     precompile_bls_map_fp_to_g1_def, precompile_bls_map_fp2_to_g2_def,
     precompile_p256verify_def]
  \\ plain_tac []
QED

Theorem plain_handle_create[local,simp]:
  plain (handle_create e)
Proof
  rw[handle_create_def] \\ plain_tac []
QED

Theorem plain_expand_memory_0[local,simp]:
  plain (expand_memory 0)
Proof
  rw[preserves_def, expand_memory_def, bind_def, get_current_context_def,
     set_current_context_def, return_def, fail_def]
  \\ gvs[AllCaseEqs(), frame_rel_def]
QED

(* -------------------------------------------------------------------------
 * The operations of a step that grow memory.
 * ------------------------------------------------------------------------- *)

Theorem max_expansion_range_le[local]:
  max_expansion_range (o1, s1) (o2, s2) = (off, sz) ⇒
  (0 < s1 ⇒ 0 < sz ∧ o1 + s1 ≤ off + sz) ∧
  (0 < s2 ⇒ 0 < sz ∧ o2 + s2 ≤ off + sz)
Proof
  rw[max_expansion_range_def] \\ gvs[AllCaseEqs()]
QED

Theorem hoare_memory_steps[local]:
  hoare (paid_at n l) step_keccak256 (λx. paid_inv 0) ∧
  hoare (paid_at n l) step_mload (λx. paid_inv 0) ∧
  hoare (paid_at n l) (step_mstore MStore) (λx. paid_inv 0) ∧
  hoare (paid_at n l) (step_mstore MStore8) (λx. paid_inv 0) ∧
  hoare (paid_at n l) (step_log k) (λx. paid_inv 0) ∧
  hoare (paid_at n l) (step_return b) (λx. paid_inv 0)
Proof
  rw[step_keccak256_def, step_mload_def, step_mstore_def, step_log_def,
     step_return_def]
  \\ hoare_tac
QED

Theorem hoare_copy_to_memory[local]:
  (∀f. src = SOME f ⇒ plain f) ⇒
  hoare (paid_at n l) (copy_to_memory gas off soff sz src) (λx. paid_inv 0)
Proof
  strip_tac \\ Cases_on `src` \\ gvs[copy_to_memory_def]
  \\ hoare_tac
  \\ Cases_on `sz` \\ gvs[]
  \\ drule max_expansion_range_le \\ rw[]
  \\ disj2_tac \\ disj2_tac \\ irule LESS_EQ_TRANS
  \\ qexists_tac `xOffset + xSize` \\ simp[]
QED

Theorem hoare_copy_steps[local]:
  hoare (paid_at n l) (step_copy_to_memory CallDataCopy (SOME get_call_data))
    (λx. paid_inv 0) ∧
  hoare (paid_at n l) (step_copy_to_memory CodeCopy (SOME get_current_code))
    (λx. paid_inv 0) ∧
  hoare (paid_at n l) (step_copy_to_memory MCopy NONE) (λx. paid_inv 0) ∧
  hoare (paid_at n l) step_return_data_copy (λx. paid_inv 0) ∧
  hoare (paid_at n l) step_ext_code_copy (λx. paid_inv 0)
Proof
  rw[step_copy_to_memory_def, step_return_data_copy_def,
     step_ext_code_copy_def]
  \\ rpt (irule hb_plain \\ rw[]) \\ irule hoare_copy_to_memory \\ rw[]
  \\ rw[get_return_data_check_def, get_code_def] \\ plain_tac []
QED

(* -------------------------------------------------------------------------
 * Calls and creates.
 * ------------------------------------------------------------------------- *)

Theorem call_gas_stipend_le[local]:
  call_gas v g gl m e = (q, r) ∧ (0 < v ⇒ call_stipend ≤ e) ⇒ r ≤ q
Proof
  rw[call_gas_def] \\ gvs[] \\ Cases_on `v` \\ gvs[]
QED

val call_simps = [initial_context_def, initial_msg_params_def];

Theorem hoare_abort_unuse[local]:
  k ≤ n ⇒ hoare (paid_at n l) (abort_unuse k) (λx. paid_inv 0)
Proof
  rw[abort_unuse_def] \\ hoare_tac
QED

Theorem hoare_abort_call_value[local]:
  k ≤ n ⇒ hoare (paid_at n l) (abort_call_value k) (λx. paid_inv 0)
Proof
  rw[abort_call_value_def] \\ hoare_tac
QED

Theorem hoare_proceed_call[local]:
  stipend ≤ n ∧ (0 < rz ⇒ ro + rz ≤ l) ⇒
  hoare (paid_at n l)
    (proceed_call op sender address value aOff aSz code stipend
       (Memory <| offset := ro; size := rz |>)) (λx. paid_inv 0)
Proof
  rw[proceed_call_def] \\ hoare_tac_with call_simps \\ gvs[]
QED

Theorem le_word_size_32_trans[local,simp]:
  x ≤ n ⇒ x ≤ 32 * word_size n
Proof
  strip_tac \\ irule LESS_EQ_TRANS \\ qexists_tac `n` \\ simp[]
QED

val call_rules = [hoare_proceed_call, hoare_abort_call_value, hoare_abort_unuse];

Theorem hoare_step_call[local]:
  hoare (paid_at n l) (step_call op) (λx. paid_inv 0)
Proof
  rw[step_call_def]
  \\ hoare_steps call_rules 3
  \\ hoare_steps call_rules 3
  \\ hoare_steps call_rules 3
  \\ hoare_steps call_rules 3
  \\ hoare_steps call_rules 3
  \\ hoare_steps call_rules 3
  \\ hoare_steps call_rules 3
  \\ hoare_steps call_rules 3
  \\ hoare_steps call_rules 3
  \\ hoare_steps call_rules 3
  \\ gvs[] \\ imp_res_tac max_expansion_range_le
  \\ imp_res_tac call_gas_stipend_le
  \\ gvs[call_value_cost_def, call_stipend_def]
QED

Theorem plain_abort_create_exists[local,simp]:
  plain (abort_create_exists a)
Proof
  rw[abort_create_exists_def]
QED

Theorem hoare_proceed_create[local]:
  k ≤ n ⇒
  hoare (paid_at n l) (proceed_create sa a v code k) (λx. paid_inv 0)
Proof
  rw[proceed_create_def] \\ hoare_tac_with call_simps \\ gvs[]
QED

val create_rules = [hoare_proceed_create, hoare_abort_unuse];

Theorem hoare_step_create[local]:
  hoare (paid_at n l) (step_create two) (λx. paid_inv 0)
Proof
  rw[step_create_def]
  \\ hoare_steps create_rules 3
  \\ hoare_steps create_rules 3
  \\ hoare_steps create_rules 3
  \\ hoare_steps create_rules 3
  \\ hoare_steps create_rules 3
  \\ hoare_steps create_rules 3
  \\ hoare_steps create_rules 3
  \\ hoare_steps create_rules 3
  \\ hoare_steps create_rules 3
  \\ hoare_steps create_rules 3
  \\ gvs[]
QED

Theorem hoare_step_inst[local]:
  hoare (paid_at n l) (step_inst op) (λx. paid_inv 0)
Proof
  Cases_on `op` \\ rw[step_inst_def]
  \\ simp[hoare_memory_steps, hoare_copy_steps, hoare_step_call,
          hoare_step_create]
  \\ irule ht_plain \\ simp[]
QED

(* -------------------------------------------------------------------------
 * Returning from a frame.
 * ------------------------------------------------------------------------- *)

Theorem pop_and_incorporate_paid[local]:
  paid_inv 0 s ∧ s.contexts = (c, crb) :: (p, prb) :: rest ∧
  pop_and_incorporate_context b s = (r, s') ⇒
  r = INL () ∧ paid_at 0 (buffer_length p.memory) s' ∧
  output_fits c (FST (HD s'.contexts))
Proof
  strip_tac
  \\ `c.msgParams.gasLimit − c.gasUsed ≤ p.gasUsed ∧
      p.gasUsed ≤ p.msgParams.gasLimit`
       by gvs[paid_inv_def, frames_paid_def]
  \\ Cases_on `b`
  \\ gvs[pop_and_incorporate_context_def, get_gas_left_def, pop_context_def,
         unuse_gas_def, push_logs_def, update_gas_refund_def,
         set_rollback_def, bind_def, ignore_bind_def,
         get_current_context_def, set_current_context_def, assert_def,
         return_def, fail_def]
  \\ gvs[paid_at_def, paid_inv_def, frames_paid_def]
  \\ Cases_on `rest` \\ gvs[outputs_fit_def, output_fits_def]
QED

Theorem hoare_reraise[local]:
  (∀s. P s ⇒ paid_inv 0 s) ⇒ hoare P (reraise e) Q
Proof
  rw[hoare_def, reraise_def]
QED

Theorem hb_get_num_contexts[local]:
  (∀k. hoare (λs. P s ∧ LENGTH s.contexts = k) (f k) Q) ⇒
  hoare P (bind get_num_contexts f) Q
Proof
  rw[hoare_def, bind_def, get_num_contexts_def, return_def]
  \\ first_x_assum (qspec_then `LENGTH s.contexts` mp_tac)
  \\ disch_then (qspec_then `s` mp_tac) \\ simp[]
QED

Theorem hb_get_return_data[local]:
  (∀s. P s ⇒ s.contexts ≠ []) ∧ (∀x. hoare P (f x) Q) ⇒
  hoare P (bind get_return_data f) Q
Proof
  rw[hoare_def, bind_def, get_return_data_def, get_current_context_def,
     return_def]
  \\ res_tac \\ gvs[]
QED

(* Returning to the caller: the output region fits the caller's memory. *)
Theorem hb_output_pop[local]:
  (∀s. P s ⇒ paid_inv 0 s ∧ 2 ≤ LENGTH s.contexts) ∧
  (∀ot l. (∀r. ot = Memory r ∧ 0 < r.size ⇒ r.offset + r.size ≤ l) ⇒
          hoare (paid_at 0 l) (g ot) Q) ⇒
  hoare P
    (bind get_output_to
       (λot. ignore_bind (pop_and_incorporate_context b) (g ot))) Q
Proof
  rw[hoare_def, ignore_bind_def, bind_def, get_output_to_def,
     get_current_context_def, return_def]
  \\ first_x_assum drule \\ strip_tac
  \\ Cases_on `s.contexts` \\ gvs[] \\ Cases_on `t` \\ gvs[]
  \\ PairCases_on `h` \\ PairCases_on `h'`
  \\ Cases_on `pop_and_incorporate_context b s`
  \\ drule_all pop_and_incorporate_paid \\ strip_tac \\ gvs[]
  \\ first_x_assum (qspecl_then [`h0.msgParams.outputTo`,
                                  `buffer_length h'0.memory`] mp_tac)
  \\ impl_tac >- gvs[output_fits_def, paid_at_def]
  \\ disch_then drule \\ simp[]
QED

Theorem ht_write_take[local]:
  (0 < sz ⇒ off + sz ≤ l) ⇒
  hoare (paid_at n l) (write_memory off (TAKE sz bs)) (λx. paid_inv 0)
Proof
  strip_tac \\ irule ht_write \\ Cases_on `sz` \\ gvs[]
  \\ rw[LENGTH_TAKE_EQ]
QED

Theorem hoare_handle_exception[local]:
  hoare (paid_inv 0) (handle_exception e) (λx. paid_inv 0)
Proof
  rewrite_tac[handle_exception_def, LET_THM] \\ BETA_TAC
  \\ irule hoare_ignore_bind \\ qexists_tac `λx. paid_inv 0`
  \\ reverse conj_tac
  >- (irule hoare_paid_inv \\ rw[] \\ irule ht_plain \\ rw[])
  \\ rw[] \\ irule hb_get_num_contexts \\ rw[]
  >- (irule hoare_reraise \\ rw[])
  \\ match_mp_tac hb_get_return_data \\ conj_tac
  >- (rw[] \\ gvs[paid_inv_def])
  \\ rw[] \\ ho_match_mp_tac hb_output_pop \\ conj_tac >- rw[]
  \\ rw[] \\ rpt (hoare_step_with [ht_write_take] [])
QED

(* -------------------------------------------------------------------------
 * A step, and the initial state.
 * ------------------------------------------------------------------------- *)

Theorem hoare_step[local]:
  hoare (paid_inv 0) step (λx. paid_inv 0)
Proof
  rw[step_def] \\ match_mp_tac hoare_handle \\ reverse conj_tac
  >- (rw[handle_step_def]
      >- (irule hoare_reraise \\ rw[])
      \\ match_mp_tac hoare_handle \\ rw[hoare_handle_exception]
      \\ irule hoare_paid_inv \\ rw[] \\ irule ht_plain \\ rw[])
  \\ irule hoare_paid_inv \\ rw[]
  \\ irule hb_plain \\ rw[]
  \\ CASE_TAC \\ rw[hoare_step_inst]
  \\ irule hoare_ignore_bind \\ qexists_tac `λx. paid_inv 0`
  \\ rw[hoare_step_inst]
  \\ irule hoare_paid_inv \\ rw[] \\ irule ht_plain \\ rw[]
QED

Theorem calldata_bounded_paid_inv[local]:
  wf_state s ∧ calldata_bounded s ⇒ paid_inv 0 s
Proof
  rw[wf_state_def, calldata_bounded_def, memory_paid_def, paid_inv_def]
  \\ gvs[EVERY_MAP, EVERY_MEM, wf_context_def]
QED

Theorem paid_inv_calldata_bounded[local]:
  paid_inv 0 s ⇒ calldata_bounded s
Proof
  rw[paid_inv_def, calldata_bounded_def, memory_paid_def]
  \\ gvs[EVERY_MEM]
QED

Theorem step_calldata_bounded:
  wf_state s ∧ calldata_bounded s ⇒ calldata_bounded (SND (step s))
Proof
  strip_tac \\ drule_all calldata_bounded_paid_inv \\ strip_tac
  \\ irule paid_inv_calldata_bounded
  \\ mp_tac hoare_step \\ rw[hoare_def]
  \\ first_x_assum drule \\ Cases_on `step s` \\ Cases_on `q` \\ rw[]
QED

Theorem pre_transaction_updates_gas_limit[local]:
  pre_transaction_updates accs b t = SOME accs' ⇒ t.gasLimit ≤ 2 ** 24
Proof
  rw[pre_transaction_updates_def, CaseEq"bool"]
QED

Theorem initial_state_calldata_bounded:
  initial_state dom static chainId prevHashes blk accs tx = SOME s ⇒
  calldata_bounded s
Proof
  strip_tac \\ gvs[initial_state_def, AllCaseEqs()]
  \\ rpt (pairarg_tac \\ gvs[])
  \\ imp_res_tac pre_transaction_updates_data_length
  \\ imp_res_tac pre_transaction_updates_gas_limit
  \\ gvs[apply_intrinsic_cost_def, AllCaseEqs(), calldata_bounded_def,
         memory_paid_def, initial_context_def, initial_msg_params_def,
         frames_paid_def, outputs_fit_def]
  \\ rw[]
QED

(* -------------------------------------------------------------------------
 * What the invariant gives for one frame.
 * ------------------------------------------------------------------------- *)

Theorem calldata_bounded_top:
  calldata_bounded s ∧ s.contexts ≠ [] ⇒
  buffer_length (FST (HD s.contexts)).msgParams.data < 2 ** 64 ∧
  (FST (HD s.contexts)).msgParams.gasLimit < 2 ** 64
Proof
  rw[calldata_bounded_def] \\ Cases_on `s.contexts` \\ gvs[]
QED

Theorem frames_paid_MEM[local]:
  ∀cs n c. frames_paid n cs ∧ MEM c cs ⇒
           memory_cost (buffer_length c.memory) ≤ c.gasUsed
Proof
  Induct \\ rw[frames_paid_def] \\ res_tac \\ simp[]
QED

Theorem calldata_bounded_memory:
  wf_state s ∧ calldata_bounded s ∧ MEM c (MAP FST s.contexts) ⇒
  buffer_length c.memory < 2 ** 64
Proof
  strip_tac \\ drule_all calldata_bounded_paid_inv
  \\ rw[paid_inv_def] \\ drule_all frames_paid_MEM \\ strip_tac
  \\ gvs[EVERY_MEM] \\ first_x_assum drule \\ strip_tac
  \\ mp_tac (Q.INST [`n` |-> `buffer_length c.memory`,
                    `g` |-> `c.msgParams.gasLimit`] memory_cost_le_lt_2_64)
  \\ simp[]
QED

(* -------------------------------------------------------------------------
 * The data of the frame a step pushes, under wf_state alone.
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
