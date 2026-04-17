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
(* balance is fixed and nonce only grows; storage and code are free  *)
(* (storage is written by SSTORE; code can be installed by           *)
(* `handle_create` when the current frame is a CREATE-deploy frame). *)
(* Non-callee accounts are required to be fully equal, so code of    *)
(* non-callee accounts is in particular preserved.                   *)
(* ================================================================ *)

Definition callee_local_changes_def:
  callee_local_changes callee r r' ⇔
    (∀a. a ≠ callee ⇒
         lookup_account a r'.accounts = lookup_account a r.accounts) ∧
    (∀a. a ≠ callee ⇒ r'.tStorage a = r.tStorage a) ∧
    (lookup_account callee r'.accounts).balance =
      (lookup_account callee r.accounts).balance ∧
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

(* ---------------- Pointwise rollback-writer lemmas -------------- *)

(* These are non-monadic-closure facts: `same_frame_rel` at a specific
   state when the given `address` is the head's callee. Used in
   compound-helper proofs (e.g. `step_sstore`, `abort_create_exists`)
   where the `address` is bound earlier in the monad chain and is
   separated from the write by intervening operations, so the
   bundled "get_callee then write" lemmas above do not apply
   syntactically. *)

Theorem write_storage_same_frame:
  s.contexts ≠ [] ∧
  address = (FST (HD s.contexts)).msgParams.callee ⇒
  same_frame_rel s (SND (write_storage address key value s))
Proof
  rw[write_storage_def, update_accounts_def, return_def]
  \\ rw[same_frame_rel_def, callee_local_changes_def,
        lookup_account_def, update_account_def, APPLY_UPDATE_THM]
  \\ Cases_on `s.contexts` \\ gvs[]
QED

Theorem write_transient_storage_same_frame:
  s.contexts ≠ [] ∧
  address = (FST (HD s.contexts)).msgParams.callee ⇒
  same_frame_rel s (SND (write_transient_storage address key value s))
Proof
  rw[write_transient_storage_def, bind_def,
     get_tStorage_def, set_tStorage_def, return_def,
     ignore_bind_def]
  \\ rw[same_frame_rel_def, callee_local_changes_def,
        update_transient_storage_def, APPLY_UPDATE_THM]
  \\ Cases_on `s.contexts` \\ gvs[]
QED

Theorem update_accounts_increment_nonce_same_frame:
  s.contexts ≠ [] ∧
  address = (FST (HD s.contexts)).msgParams.callee ⇒
  same_frame_rel s
    (SND (update_accounts (increment_nonce address) s))
Proof
  rw[update_accounts_def, return_def, increment_nonce_def]
  \\ rw[same_frame_rel_def, callee_local_changes_def, increment_nonce_def,
        lookup_account_def, update_account_def, APPLY_UPDATE_THM]
  \\ Cases_on `s.contexts` \\ gvs[]
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

(* ================================================================ *)
(* Pass A: Compound-helper `preserves_same_frame` lemmas.            *)
(*                                                                   *)
(* Each unfolds the definition and relies on the primitive-level     *)
(* `[simp]` lemmas above plus the monadic composition lemmas.        *)
(* ================================================================ *)

Theorem preserves_same_frame_step_binop[simp]:
  preserves_same_frame (step_binop op f)
Proof
  rw[step_binop_def]
QED

Theorem preserves_same_frame_step_monop[simp]:
  preserves_same_frame (step_monop op f)
Proof
  rw[step_monop_def]
QED

Theorem preserves_same_frame_step_modop[simp]:
  preserves_same_frame (step_modop op f)
Proof
  rw[step_modop_def]
QED

Theorem preserves_same_frame_step_context[simp]:
  preserves_same_frame (step_context op f)
Proof
  rw[step_context_def]
QED

Theorem preserves_same_frame_step_msgParams[simp]:
  preserves_same_frame (step_msgParams op f)
Proof
  rw[step_msgParams_def]
QED

Theorem preserves_same_frame_step_txParams[simp]:
  preserves_same_frame (step_txParams op f)
Proof
  rw[step_txParams_def]
QED

Theorem preserves_same_frame_step_exp[simp]:
  preserves_same_frame step_exp
Proof
  rw[step_exp_def]
QED

Theorem preserves_same_frame_step_keccak256[simp]:
  preserves_same_frame step_keccak256
Proof
  rw[step_keccak256_def] >>
  irule preserves_same_frame_bind >> rw[]
QED

Theorem preserves_same_frame_step_sload[simp]:
  preserves_same_frame (step_sload t)
Proof
  rw[step_sload_def] >>
  irule preserves_same_frame_bind >> rw[] >>
  irule preserves_same_frame_bind >> rw[]
QED

Theorem preserves_same_frame_step_sstore_gas_consumption[simp]:
  preserves_same_frame (step_sstore_gas_consumption a k v)
Proof
  rw[step_sstore_gas_consumption_def] >>
  irule preserves_same_frame_bind >> rw[] >>
  irule preserves_same_frame_ignore_bind >> rw[]
QED

(* `preserves_same_frame (step_sstore transient)` and the SSTORE/TSTORE
   cases of `step_inst` are handled directly inside `step_same_frame`
   (see Pass D) via the pointwise lemmas `write_storage_same_frame`
   and `write_transient_storage_same_frame` above. A standalone helper
   lemma would require threading the `address = head's callee` invariant
   through intervening monadic operations, which is more awkward than
   reasoning about the whole chain in one place. *)

Theorem preserves_same_frame_step_balance[simp]:
  preserves_same_frame step_balance
Proof
  rw[step_balance_def]
QED

Theorem preserves_same_frame_step_call_data_load[simp]:
  preserves_same_frame step_call_data_load
Proof
  rw[step_call_data_load_def]
QED

Theorem preserves_same_frame_copy_to_memory:
  (∀f. src = SOME f ⇒ preserves_same_frame f) ⇒
  preserves_same_frame (copy_to_memory gas off srcOff sz src)
Proof
  Cases_on `src` \\ rw[copy_to_memory_def]
  \\ TRY pairarg_tac >> simp[]
  \\ rpt (irule preserves_same_frame_bind \\ rw[])
QED

Theorem preserves_same_frame_step_copy_to_memory[simp]:
  (∀f. src = SOME f ⇒ preserves_same_frame f) ⇒
  preserves_same_frame (step_copy_to_memory op src)
Proof
  rw[step_copy_to_memory_def]
  \\ rpt (irule preserves_same_frame_bind \\ rw[])
  \\ rpt (irule preserves_same_frame_ignore_bind \\ rw[])
  \\ irule preserves_same_frame_copy_to_memory \\ simp[]
QED

Theorem preserves_same_frame_step_return_data_copy[simp]:
  preserves_same_frame step_return_data_copy
Proof
  rw[step_return_data_copy_def]
  \\ rpt (irule preserves_same_frame_bind \\ rw[])
  \\ rpt (irule preserves_same_frame_ignore_bind \\ rw[])
  \\ irule preserves_same_frame_copy_to_memory \\ simp[]
QED

Theorem preserves_same_frame_step_ext_code_size[simp]:
  preserves_same_frame step_ext_code_size
Proof
  rw[step_ext_code_size_def]
QED

Theorem preserves_same_frame_step_ext_code_copy[simp]:
  preserves_same_frame step_ext_code_copy
Proof
  rw[step_ext_code_copy_def]
  \\ rpt (irule preserves_same_frame_bind \\ rw[])
  \\ rpt (irule preserves_same_frame_ignore_bind \\ rw[])
  \\ irule preserves_same_frame_copy_to_memory \\ simp[]
QED

Theorem preserves_same_frame_step_ext_code_hash[simp]:
  preserves_same_frame step_ext_code_hash
Proof
  rw[step_ext_code_hash_def]
QED

Theorem preserves_same_frame_step_block_hash[simp]:
  preserves_same_frame step_block_hash
Proof
  rw[step_block_hash_def]
QED

Theorem preserves_same_frame_step_blob_hash[simp]:
  preserves_same_frame step_blob_hash
Proof
  rw[step_blob_hash_def]
QED

Theorem preserves_same_frame_step_self_balance[simp]:
  preserves_same_frame step_self_balance
Proof
  rw[step_self_balance_def]
QED

Theorem preserves_same_frame_step_mload[simp]:
  preserves_same_frame step_mload
Proof
  rw[step_mload_def]
  \\ irule preserves_same_frame_bind >> rw[]
QED

Theorem preserves_same_frame_step_mstore[simp]:
  preserves_same_frame (step_mstore op)
Proof
  rw[step_mstore_def]
QED

Theorem preserves_same_frame_step_jump[simp]:
  preserves_same_frame step_jump
Proof
  rw[step_jump_def]
QED

Theorem preserves_same_frame_step_jumpi[simp]:
  preserves_same_frame step_jumpi
Proof
  rw[step_jumpi_def]
QED

Theorem preserves_same_frame_step_push[simp]:
  preserves_same_frame (step_push n ws)
Proof
  rw[step_push_def]
QED

Theorem preserves_same_frame_step_pop[simp]:
  preserves_same_frame step_pop
Proof
  rw[step_pop_def]
QED

Theorem preserves_same_frame_step_dup[simp]:
  preserves_same_frame (step_dup n)
Proof
  rw[step_dup_def]
  \\ rpt (irule preserves_same_frame_bind \\ rw[])
  \\ rpt (irule preserves_same_frame_ignore_bind \\ rw[])
QED

Theorem preserves_same_frame_step_swap[simp]:
  preserves_same_frame (step_swap n)
Proof
  rw[step_swap_def]
  \\ irule preserves_same_frame_ignore_bind >> rw[]
  \\ rw[preserves_same_frame_def, set_current_context_def,
        return_def, fail_def, bind_def, ignore_bind_def]
  \\ gvs[AllCaseEqs(), assert_def, get_current_context_def, return_def]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ rw[same_frame_rel_def, callee_local_changes_def]
QED

Theorem preserves_same_frame_step_log[simp]:
  preserves_same_frame (step_log n)
Proof
  rw[step_log_def]
  \\ irule preserves_same_frame_bind >> rw[]
  \\ irule preserves_same_frame_bind >> rw[]
  \\ irule preserves_same_frame_ignore_bind >> rw[]
QED

Theorem preserves_same_frame_step_return[simp]:
  preserves_same_frame (step_return b)
Proof
  rw[step_return_def]
  \\ rpt (irule preserves_same_frame_bind \\ rw[])
  \\ rpt (irule preserves_same_frame_ignore_bind \\ rw[])
  \\ Cases_on `b` \\ rw[]
QED

Theorem preserves_same_frame_inc_pc_or_jump[simp]:
  preserves_same_frame (inc_pc_or_jump op)
Proof
  rw[inc_pc_or_jump_def]
  \\ rw[preserves_same_frame_def, set_current_context_def, return_def,
        fail_def, bind_def] >>
  gvs[AllCaseEqs(), get_current_context_def, return_def]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ gvs[vfmTypesTheory.option_CASE_rator, AllCaseEqs(),
         set_current_context_def, return_def]
  >- (rw[same_frame_rel_def, callee_local_changes_def])
  \\ gvs[ignore_bind_def, bind_def, AllCaseEqs(), assert_def]
  \\ gvs[set_current_context_def, return_def]
  \\ rw[same_frame_rel_def, callee_local_changes_def]
QED

Theorem preserves_same_frame_abort_unuse[simp]:
  preserves_same_frame (abort_unuse n)
Proof
  rw[abort_unuse_def]
QED

Theorem preserves_same_frame_abort_call_value[simp]:
  preserves_same_frame (abort_call_value n)
Proof
  rw[abort_call_value_def]
QED

(* `abort_create_exists senderAddress` takes `senderAddress` as an
   arbitrary parameter. A `preserves_same_frame` statement with no
   side condition would be false: if `senderAddress` is not the head's
   callee, the `update_accounts (increment_nonce senderAddress)` step
   modifies a non-callee account's nonce, violating
   `callee_local_changes`. In its sole call site (`step_create`),
   `senderAddress` was bound from `get_callee`, so the invariant
   holds — we prove this directly inside `step_same_frame`'s
   CREATE-abort branch (see Pass D) via the pointwise
   `update_accounts_increment_nonce_same_frame` lemma above. *)

(* --- Precompiles --- *)

Theorem preserves_same_frame_precompile_ecrecover[simp]:
  preserves_same_frame precompile_ecrecover
Proof
  rw[precompile_ecrecover_def]
  \\ rpt (irule preserves_same_frame_bind \\ rw[])
  \\ rpt (irule preserves_same_frame_ignore_bind \\ rw[])
  \\ Cases_on `ecrecover hash v r s'` \\ rw[]
  \\ rpt (irule preserves_same_frame_bind \\ rw[])
  \\ rpt (irule preserves_same_frame_ignore_bind \\ rw[])
QED

Theorem preserves_same_frame_precompile_sha2_256[simp]:
  preserves_same_frame precompile_sha2_256
Proof
  rw[precompile_sha2_256_def]
QED

Theorem preserves_same_frame_precompile_ripemd_160[simp]:
  preserves_same_frame precompile_ripemd_160
Proof
  rw[precompile_ripemd_160_def]
QED

Theorem preserves_same_frame_precompile_identity[simp]:
  preserves_same_frame precompile_identity
Proof
  rw[precompile_identity_def]
QED

Theorem preserves_same_frame_precompile_modexp[simp]:
  preserves_same_frame precompile_modexp
Proof
  rw[precompile_modexp_def]
QED

Theorem preserves_same_frame_precompile_ecadd[simp]:
  preserves_same_frame precompile_ecadd
Proof
  rw[precompile_ecadd_def]
  \\ irule preserves_same_frame_bind >> rw[]
QED

Theorem preserves_same_frame_precompile_ecmul[simp]:
  preserves_same_frame precompile_ecmul
Proof
  rw[precompile_ecmul_def]
  \\ irule preserves_same_frame_bind >> rw[]
QED

Theorem preserves_same_frame_precompile_ecpairing[simp]:
  preserves_same_frame precompile_ecpairing
Proof
  rw[precompile_ecpairing_def]
  \\ irule preserves_same_frame_bind >> rw[]
QED

Theorem preserves_same_frame_precompile_blake2f[simp]:
  preserves_same_frame precompile_blake2f
Proof
  rw[precompile_blake2f_def]
  \\ irule preserves_same_frame_bind >> rw[]
QED

Theorem preserves_same_frame_precompile_point_eval[simp]:
  preserves_same_frame precompile_point_eval
Proof
  rw[precompile_point_eval_def]
  \\ irule preserves_same_frame_bind >> rw[]
  \\ irule preserves_same_frame_ignore_bind >> rw[]
  \\ irule preserves_same_frame_ignore_bind >> rw[]
  \\ irule preserves_same_frame_ignore_bind >> rw[]
QED

Theorem preserves_same_frame_precompile_bls_g1add[simp]:
  preserves_same_frame precompile_bls_g1add
Proof
  rw[precompile_bls_g1add_def]
QED

Theorem preserves_same_frame_precompile_bls_g1msm[simp]:
  preserves_same_frame precompile_bls_g1msm
Proof
  rw[precompile_bls_g1msm_def]
QED

Theorem preserves_same_frame_precompile_bls_g2add[simp]:
  preserves_same_frame precompile_bls_g2add
Proof
  rw[precompile_bls_g2add_def]
QED

Theorem preserves_same_frame_precompile_bls_g2msm[simp]:
  preserves_same_frame precompile_bls_g2msm
Proof
  rw[precompile_bls_g2msm_def]
QED

Theorem preserves_same_frame_precompile_bls_pairing[simp]:
  preserves_same_frame precompile_bls_pairing
Proof
  rw[precompile_bls_pairing_def]
QED

Theorem preserves_same_frame_precompile_bls_map_fp_to_g1[simp]:
  preserves_same_frame precompile_bls_map_fp_to_g1
Proof
  rw[precompile_bls_map_fp_to_g1_def]
QED

Theorem preserves_same_frame_precompile_bls_map_fp2_to_g2[simp]:
  preserves_same_frame precompile_bls_map_fp2_to_g2
Proof
  rw[precompile_bls_map_fp2_to_g2_def]
QED

Theorem preserves_same_frame_precompile_p256verify[simp]:
  preserves_same_frame precompile_p256verify
Proof
  rw[precompile_p256verify_def]
  >> irule preserves_same_frame_bind >> rw[]
QED

Theorem preserves_same_frame_dispatch_precompiles[simp]:
  preserves_same_frame (dispatch_precompiles a)
Proof
  rw[dispatch_precompiles_def]
QED
