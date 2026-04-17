(*
 * Same-frame preservation framework.
 *
 * `same_frame_rel s s'` is a relation expressing what necessarily holds
 * between states `s` and `s'` whenever `s'` is reached from `s` by
 * execution that does not push or pop the call stack — i.e. while
 * staying strictly within the current call frame.
 *
 * Downstream theories use this relation (plus its reflexivity and
 * transitivity, proved here) to lift preservation properties through
 * `run_within_frame`, `run_call`, and the full `run`.
 *)
Theory vfmCallFrame
Ancestors
  arithmetic combin list pair pred_set finite_set rich_list
  vfmState vfmContext vfmExecution vfmExecutionProp
  vfmStaticCalls vfmTxParams vfmDomainSeparation
Libs
  BasicProvers

val _ = Parse.hide "add"

(* ================================================================ *)
(* Helper: compatibility of the metadata-domain field.              *)
(* In `Enforce d` mode, `d` is never written by any monadic         *)
(* primitive (it is only checked); in `Collect d` mode, `d` only    *)
(* grows. This captures both cases uniformly.                       *)
(* ================================================================ *)

Definition msdomain_compatible_def:
  msdomain_compatible m1 m2 ⇔
    case (m1, m2) of
    | (Enforce d1, Enforce d2) => d1 = d2
    | (Collect d1, Collect d2) => subdomain d1 d2
    | _ => F
End

Theorem msdomain_compatible_refl[simp]:
  msdomain_compatible m m
Proof
  rw[msdomain_compatible_def]
  \\ CASE_TAC \\ rw[]
QED

Theorem msdomain_compatible_trans:
  msdomain_compatible m1 m2 ∧ msdomain_compatible m2 m3 ⇒
  msdomain_compatible m1 m3
Proof
  rw[msdomain_compatible_def]
  \\ every_case_tac \\ gvs[]
  \\ metis_tac[subdomain_trans]
QED

(* ================================================================ *)
(* Callee-local account/tStorage changes permitted within a frame.   *)
(*                                                                   *)
(* Within one call frame, only the callee's account and its          *)
(* transient storage slots may be written. Even at the callee,       *)
(* balance and code stay fixed and nonce only grows.                 *)
(* ================================================================ *)

Definition callee_local_changes_def:
  callee_local_changes callee r r' ⇔
    (∀a. a ≠ callee ⇒
         lookup_account a r'.accounts = lookup_account a r.accounts) ∧
    (∀a. a ≠ callee ⇒ r'.tStorage a = r.tStorage a) ∧
    (lookup_account callee r'.accounts).balance =
      (lookup_account callee r.accounts).balance ∧
    (lookup_account callee r'.accounts).code =
      (lookup_account callee r.accounts).code ∧
    (lookup_account callee r.accounts).nonce ≤
      (lookup_account callee r'.accounts).nonce
End

Theorem callee_local_changes_refl[simp]:
  callee_local_changes callee r r
Proof
  rw[callee_local_changes_def]
QED

Theorem callee_local_changes_trans:
  callee_local_changes callee r1 r2 ∧
  callee_local_changes callee r2 r3 ⇒
  callee_local_changes callee r1 r3
Proof
  rw[callee_local_changes_def]
  \\ metis_tac[LESS_EQ_TRANS]
QED

(* ================================================================ *)
(* The same-frame relation.                                          *)
(* ================================================================ *)

Definition same_frame_rel_def:
  same_frame_rel s s' ⇔
    s.contexts ≠ [] ∧
    LENGTH s'.contexts = LENGTH s.contexts ∧
    TL s'.contexts = TL s.contexts ∧
    SND (HD s'.contexts) = SND (HD s.contexts) ∧
    (FST (HD s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams ∧
    s'.txParams = s.txParams ∧
    s'.rollback.toDelete = s.rollback.toDelete ∧
    callee_local_changes
      (FST (HD s.contexts)).msgParams.callee
      s.rollback s'.rollback ∧
    toSet s.rollback.accesses.addresses ⊆
      toSet s'.rollback.accesses.addresses ∧
    toSet s.rollback.accesses.storageKeys ⊆
      toSet s'.rollback.accesses.storageKeys ∧
    msdomain_compatible s.msdomain s'.msdomain ∧
    IS_PREFIX (FST (HD s'.contexts)).logs (FST (HD s.contexts)).logs ∧
    (FST (HD s.contexts)).addRefund ≤ (FST (HD s'.contexts)).addRefund ∧
    (FST (HD s.contexts)).subRefund ≤ (FST (HD s'.contexts)).subRefund
End

(* ================================================================ *)
(* Reflexivity.                                                      *)
(* ================================================================ *)

Theorem same_frame_rel_refl:
  s.contexts ≠ [] ⇒ same_frame_rel s s
Proof
  rw[same_frame_rel_def]
QED

(* ================================================================ *)
(* Transitivity.                                                     *)
(* ================================================================ *)

Theorem same_frame_rel_trans:
  same_frame_rel s1 s2 ∧ same_frame_rel s2 s3 ⇒
  same_frame_rel s1 s3
Proof
  rw[same_frame_rel_def]
  \\ gvs[]
  \\ TRY (metis_tac[SUBSET_TRANS, msdomain_compatible_trans,
                    IS_PREFIX_TRANS, LESS_EQ_TRANS,
                    callee_local_changes_trans])
QED

Theorem same_frame_rel_contexts_ne:
  same_frame_rel s s' ⇒ s'.contexts ≠ []
Proof
  rw[same_frame_rel_def]
  \\ strip_tac \\ gvs[]
QED

(* ================================================================ *)
(* `preserves_same_frame`: a monad-level property expressing that    *)
(* running `m` from any non-empty-contexts state yields a state      *)
(* related to the starting state by `same_frame_rel`.                *)
(*                                                                   *)
(* Structured like `cp` in vfmStaticCalls: composition lemmas first, *)
(* then primitive-level lemmas (Step 2c), then opcode-level          *)
(* (Step 2d).                                                        *)
(* ================================================================ *)

Definition preserves_same_frame_def:
  preserves_same_frame (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ∧ s.contexts ≠ [] ⇒ same_frame_rel s s'
End

(* ---------------- Composition lemmas ---------------- *)

Theorem preserves_same_frame_bind[simp]:
  preserves_same_frame g ∧ (∀x. preserves_same_frame (f x)) ⇒
  preserves_same_frame (bind g f)
Proof
  rw[preserves_same_frame_def, bind_def]
  \\ gvs[AllCaseEqs()]
  \\ irule same_frame_rel_trans
  \\ first_x_assum drule
  \\ first_x_assum drule \\ rw[]
  \\ drule same_frame_rel_contexts_ne \\ rw[] \\ gvs[]
  \\ goal_assum drule \\ rw[]
QED

Theorem preserves_same_frame_ignore_bind[simp]:
  preserves_same_frame g ∧ preserves_same_frame f ⇒
  preserves_same_frame (ignore_bind g f)
Proof
  rw[ignore_bind_def] \\ irule preserves_same_frame_bind \\ simp[]
QED

Theorem preserves_same_frame_handle[simp]:
  preserves_same_frame f ∧ (∀e. preserves_same_frame (h e)) ⇒
  preserves_same_frame (handle f h)
Proof
  rw[preserves_same_frame_def, handle_def]
  \\ gvs[AllCaseEqs()]
  \\ first_x_assum drule
  \\ first_x_assum drule \\ rw[]
  \\ drule same_frame_rel_contexts_ne \\ rw[] \\ gvs[]
  \\ metis_tac[same_frame_rel_trans]
QED

Theorem preserves_same_frame_cond[simp]:
  preserves_same_frame m1 ∧ preserves_same_frame m2 ⇒
  preserves_same_frame (if b then m1 else m2)
Proof
  rw[]
QED

Theorem preserves_same_frame_case_option[simp]:
  preserves_same_frame m_none ∧ (∀x. preserves_same_frame (m_some x)) ⇒
  preserves_same_frame (case opt of NONE => m_none | SOME x => m_some x)
Proof
  Cases_on `opt` \\ rw[]
QED

Theorem preserves_same_frame_case_sum[simp]:
  (∀x. preserves_same_frame (f x)) ∧ (∀y. preserves_same_frame (g y)) ⇒
  preserves_same_frame (case s of INL x => f x | INR y => g y)
Proof
  Cases_on `s` \\ rw[]
QED

Theorem preserves_same_frame_case_pair[simp]:
  (∀x y. preserves_same_frame (f x y)) ⇒
  preserves_same_frame (case p of (x, y) => f x y)
Proof
  Cases_on `p` \\ rw[]
QED

Theorem preserves_same_frame_let[simp]:
  (∀x. preserves_same_frame (f x)) ⇒
  preserves_same_frame (let x = v in f x)
Proof
  rw[]
QED

Theorem preserves_same_frame_uncurry[simp]:
  (∀x y. preserves_same_frame (f x y)) ⇒
  preserves_same_frame (UNCURRY f p)
Proof
  Cases_on `p` \\ rw[]
QED

(* ================================================================ *)
(* Primitive-level `preserves_same_frame` lemmas.                    *)
(*                                                                   *)
(* Structure: first trivial (state-unchanged) primitives, then       *)
(* head-context-only writers, then rollback/domain writers.          *)
(*                                                                   *)
(* Operations that always push or pop a context                      *)
(* (`push_context`, `pop_context`, `set_rollback`, `add_to_delete`,  *)
(* `set_original`, `pop_and_incorporate_context`) are OUT OF SCOPE   *)
(* for this predicate: they do not satisfy `preserves_same_frame`    *)
(* and are treated at the cross-boundary layer (Step 3 / RunCall).   *)
(* ================================================================ *)

(* ---------------- Group A: state-unchanged primitives ----------- *)

(* A shared tactic: unfold to a form where the result state equals the
   input state (or a trivial variant), then close by reflexivity. *)
val psf_refl_tac =
  rw[preserves_same_frame_def]
  \\ gvs[return_def, fail_def, reraise_def, assert_def,
         finish_def, revert_def,
         get_current_context_def, get_num_contexts_def,
         get_tx_params_def, get_accounts_def, get_rollback_def,
         get_tStorage_def, get_gas_left_def, get_callee_def,
         get_caller_def, get_value_def, get_static_def,
         get_output_to_def, get_return_data_def, get_code_def,
         get_current_code_def, get_call_data_def,
         get_return_data_check_def, read_memory_def,
         memory_expansion_info_def,
         get_original_def, ok_state_def, bind_def, ignore_bind_def]
  \\ gvs[AllCaseEqs()]
  \\ irule same_frame_rel_refl \\ simp[];

Theorem preserves_same_frame_return[simp]:
  preserves_same_frame (return x)
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_fail[simp]:
  preserves_same_frame (fail e)
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_reraise[simp]:
  preserves_same_frame (reraise eo)
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_assert[simp]:
  preserves_same_frame (assert b e)
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_finish[simp]:
  preserves_same_frame finish
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_revert[simp]:
  preserves_same_frame revert
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_get_current_context[simp]:
  preserves_same_frame get_current_context
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_get_num_contexts[simp]:
  preserves_same_frame get_num_contexts
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_get_tx_params[simp]:
  preserves_same_frame get_tx_params
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_get_accounts[simp]:
  preserves_same_frame get_accounts
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_get_rollback[simp]:
  preserves_same_frame get_rollback
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_get_tStorage[simp]:
  preserves_same_frame get_tStorage
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_get_gas_left[simp]:
  preserves_same_frame get_gas_left
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_get_callee[simp]:
  preserves_same_frame get_callee
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_get_caller[simp]:
  preserves_same_frame get_caller
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_get_value[simp]:
  preserves_same_frame get_value
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_get_static[simp]:
  preserves_same_frame get_static
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_get_output_to[simp]:
  preserves_same_frame get_output_to
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_get_return_data[simp]:
  preserves_same_frame get_return_data
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_get_return_data_check[simp]:
  preserves_same_frame (get_return_data_check offset sz)
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_get_code[simp]:
  preserves_same_frame (get_code addr)
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_get_current_code[simp]:
  preserves_same_frame get_current_code
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_get_call_data[simp]:
  preserves_same_frame get_call_data
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_get_original[simp]:
  preserves_same_frame get_original
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_read_memory[simp]:
  preserves_same_frame (read_memory offset sz)
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_memory_expansion_info[simp]:
  preserves_same_frame (memory_expansion_info offset sz)
Proof
  psf_refl_tac
QED

Theorem preserves_same_frame_assert_not_static[simp]:
  preserves_same_frame assert_not_static
Proof
  rw[assert_not_static_def]
QED

(* ---------------- Group B: head-context-only writers ------------ *)

(* These writers all go through `set_current_context` with a function
   of the head context that keeps `msgParams` fixed and adjusts only
   stack/memory/pc/jumpDest/returnData/gasUsed/logs/refunds. We prove
   each explicitly. *)

val psf_head_tac =
  rw[preserves_same_frame_def, same_frame_rel_def,
     bind_def, ignore_bind_def,
     get_current_context_def, set_current_context_def, ok_state_def,
     return_def, fail_def, assert_def,
     push_stack_def, pop_stack_def,
     consume_gas_def, unuse_gas_def,
     set_return_data_def, set_jump_dest_def,
     push_logs_def, update_gas_refund_def,
     expand_memory_def, write_memory_def,
     inc_pc_def, callee_local_changes_def]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ PairCases_on `h` \\ gvs[]
  \\ rpt (BasicProvers.FULL_CASE_TAC \\ gvs[]);

Theorem preserves_same_frame_push_stack[simp]:
  preserves_same_frame (push_stack v)
Proof
  psf_head_tac
QED

Theorem preserves_same_frame_pop_stack[simp]:
  preserves_same_frame (pop_stack n)
Proof
  psf_head_tac
QED

Theorem preserves_same_frame_consume_gas[simp]:
  preserves_same_frame (consume_gas n)
Proof
  psf_head_tac
QED

Theorem preserves_same_frame_unuse_gas[simp]:
  preserves_same_frame (unuse_gas n)
Proof
  psf_head_tac
QED

Theorem preserves_same_frame_set_return_data[simp]:
  preserves_same_frame (set_return_data rd)
Proof
  psf_head_tac
QED

Theorem preserves_same_frame_set_jump_dest[simp]:
  preserves_same_frame (set_jump_dest jd)
Proof
  psf_head_tac
QED

Theorem preserves_same_frame_inc_pc[simp]:
  preserves_same_frame inc_pc
Proof
  psf_head_tac
QED

Theorem preserves_same_frame_expand_memory[simp]:
  preserves_same_frame (expand_memory n)
Proof
  psf_head_tac
QED

Theorem preserves_same_frame_write_memory[simp]:
  preserves_same_frame (write_memory i bs)
Proof
  psf_head_tac
QED

Theorem preserves_same_frame_update_gas_refund[simp]:
  preserves_same_frame (update_gas_refund ars)
Proof
  Cases_on `ars` \\ psf_head_tac
QED

Theorem preserves_same_frame_push_logs[simp]:
  preserves_same_frame (push_logs ls)
Proof
  psf_head_tac
  \\ rw[rich_listTheory.IS_PREFIX_APPEND]
  \\ metis_tac[]
QED

(* ---------------- Group C: rollback / domain writers ------------ *)

(* `set_tStorage x`: only safe if `x` differs from the current
   tStorage only at the callee slot. We parameterise on that. *)

Theorem preserves_same_frame_set_tStorage:
  (∀a. a ≠ callee ⇒ x a = t a) ⇒
  ∀s. s.contexts ≠ [] ∧ (FST (HD s.contexts)).msgParams.callee = callee ∧
      s.rollback.tStorage = t ⇒
      same_frame_rel s (SND (set_tStorage x s))
Proof
  rw[set_tStorage_def, return_def]
  \\ rw[same_frame_rel_def, callee_local_changes_def]
  \\ Cases_on `s.contexts` \\ gvs[]
QED

(* `write_transient_storage` targets the callee's slot. *)

Theorem preserves_same_frame_write_transient_storage_callee:
  preserves_same_frame
    (do addr <- get_callee;
        write_transient_storage addr key value
     od)
Proof
  rw[preserves_same_frame_def, bind_def,
     get_callee_def, get_current_context_def, ok_state_def, return_def,
     fail_def, write_transient_storage_def,
     get_tStorage_def, set_tStorage_def, ignore_bind_def]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ PairCases_on `h` \\ gvs[]
  \\ rw[same_frame_rel_def, callee_local_changes_def,
        update_transient_storage_def, APPLY_UPDATE_THM]
  \\ rw[]
QED

(* `write_storage` targets a specific account's storage; safe when
   that address is the head's callee. *)

Theorem preserves_same_frame_write_storage_callee:
  preserves_same_frame
    (do addr <- get_callee;
        write_storage addr key value
     od)
Proof
  rw[preserves_same_frame_def, bind_def,
     get_callee_def, get_current_context_def, ok_state_def, return_def,
     fail_def, write_storage_def, update_accounts_def]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ PairCases_on `h` \\ gvs[]
  \\ rw[same_frame_rel_def, callee_local_changes_def,
        lookup_account_def, update_account_def, APPLY_UPDATE_THM]
  \\ rw[]
QED

(* `update_accounts (increment_nonce callee)`: safe; increments callee
   nonce only. *)

Theorem preserves_same_frame_update_accounts_increment_nonce_callee:
  preserves_same_frame
    (do addr <- get_callee;
        update_accounts (increment_nonce addr)
     od)
Proof
  rw[preserves_same_frame_def, bind_def,
     get_callee_def, get_current_context_def, ok_state_def, return_def,
     fail_def, update_accounts_def, increment_nonce_def]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ PairCases_on `h` \\ gvs[]
  \\ rw[same_frame_rel_def, callee_local_changes_def, increment_nonce_def,
        lookup_account_def, update_account_def, APPLY_UPDATE_THM]
QED

(* ---------------- Group D: set_current_context (parameterised) -- *)

(* Replacing the head context preserves the frame iff the new context
   agrees on msgParams and logs extend, with monotone refunds. *)

Theorem preserves_same_frame_set_current_context:
  ∀s c.
    s.contexts ≠ [] ∧
    c.msgParams = (FST (HD s.contexts)).msgParams ∧
    IS_PREFIX c.logs (FST (HD s.contexts)).logs ∧
    (FST (HD s.contexts)).addRefund ≤ c.addRefund ∧
    (FST (HD s.contexts)).subRefund ≤ c.subRefund ⇒
    same_frame_rel s (SND (set_current_context c s))
Proof
  rw[set_current_context_def, return_def]
  \\ rw[same_frame_rel_def]
  \\ Cases_on `s.contexts` \\ gvs[]
QED

(* ---------------- Group E: domain / access writers -------------- *)

Theorem preserves_same_frame_set_domain:
  msdomain_compatible s.msdomain d ∧ s.contexts ≠ [] ⇒
  same_frame_rel s (SND (set_domain d s))
Proof
  rw[set_domain_def, return_def, same_frame_rel_def]
QED

(* `domain_check`: in Enforce mode it either continues via `cont` or
   fails leaving state untouched; in Collect mode it updates msdomain
   (compatibly) then runs `cont`. *)

Theorem preserves_same_frame_domain_check:
  (∀d. subdomain d (add d)) ∧
  preserves_same_frame cont ⇒
  preserves_same_frame (domain_check err check add cont)
Proof
  rw[preserves_same_frame_def, domain_check_def]
  \\ Cases_on `s.msdomain` \\ gvs[]
  >- (
    gvs[fail_def,AllCaseEqs()]
    \\ irule same_frame_rel_refl \\ simp[])
  \\ gvs[ignore_bind_def, bind_def, set_domain_def, return_def]
  \\ qmatch_asmsub_abbrev_tac`cont s1`
  \\ `same_frame_rel s s1`
     by (rw[same_frame_rel_def, msdomain_compatible_def, Abbr`s1`])
  \\ first_x_assum drule \\ impl_tac >- rw[Abbr`s1`]
  \\ metis_tac[same_frame_rel_trans]
QED

Theorem preserves_same_frame_access_address[simp]:
  preserves_same_frame (access_address a)
Proof
  rw[access_address_def]
  \\ irule preserves_same_frame_domain_check
  \\ rw[preserves_same_frame_def, return_def]
  >- ( rw[subdomain_def, toSet_fINSERT, SUBSET_DEF] )
  \\ rw[same_frame_rel_def, callee_local_changes_def]
  >- ( rw[subdomain_def, toSet_fINSERT, SUBSET_DEF] )
QED

Theorem preserves_same_frame_access_slot[simp]:
  preserves_same_frame (access_slot sk)
Proof
  rw[access_slot_def]
  \\ irule preserves_same_frame_domain_check
  \\ rw[preserves_same_frame_def, return_def]
  >- ( rw[subdomain_def, toSet_fINSERT, SUBSET_DEF] )
  \\ rw[same_frame_rel_def, callee_local_changes_def]
  >- ( rw[subdomain_def, toSet_fINSERT, SUBSET_DEF] )
QED

Theorem preserves_same_frame_ensure_storage_in_domain[simp]:
  preserves_same_frame (ensure_storage_in_domain a)
Proof
  rw[ensure_storage_in_domain_def]
  \\ irule preserves_same_frame_domain_check
  \\ rw[preserves_same_frame_def, return_def]
  >- ( rw[subdomain_def, toSet_fINSERT, SUBSET_DEF] )
QED
