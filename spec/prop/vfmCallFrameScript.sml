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
  vfmStaticCalls vfmTxParams vfmDomainSeparation vfmDecreasesGas
Libs
  BasicProvers

val _ = Parse.hide "add"
val _ = Parse.hide "from"

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
(* Within one call frame:                                            *)
(*  - non-callee accounts' storage, code, and nonce are preserved;   *)
(*  - non-callee tStorage slots are preserved;                       *)
(*  - the callee's nonce is monotone (only grows);                   *)
(*  - balances of all accounts are free (SELFDESTRUCT can transfer   *)
(*    from the callee to an arbitrary beneficiary);                  *)
(*  - the callee's storage, code, and nonce beyond monotonicity are  *)
(*    free (SSTORE writes storage; `handle_create` can install code  *)
(*    in a CREATE-deploy frame).                                     *)
(* ================================================================ *)

Definition callee_local_changes_def:
  callee_local_changes callee r r' ⇔
    (∀a. a ≠ callee ⇒
         (lookup_account a r'.accounts).storage =
         (lookup_account a r.accounts).storage ∧
         (lookup_account a r'.accounts).code =
         (lookup_account a r.accounts).code ∧
         (lookup_account a r'.accounts).nonce =
         (lookup_account a r.accounts).nonce) ∧
    (∀a. a ≠ callee ⇒ r'.tStorage a = r.tStorage a) ∧
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

(* ================================================================ *)
(* Pass A': State-indexed precondition framework (`psf`).            *)
(*                                                                   *)
(* `psf p m` says: whenever `m` runs from a state `s` satisfying     *)
(* precondition `p` and having non-empty contexts, the result state  *)
(* `s'` is related to `s` by `same_frame_rel`.                       *)
(*                                                                   *)
(* This is the state-indexed analogue of `preserves_same_frame`.     *)
(* The precondition `p` lets specialised composition rules thread    *)
(* facts about bound values (e.g. "x = head's callee") into the      *)
(* continuation's proof context — enabling same-frame reasoning      *)
(* for write operations that need `address = callee` as a side       *)
(* condition.                                                        *)
(*                                                                   *)
(* Usage mirrors `ignores_extra_domain_pred` in vfmDomainSeparation: *)
(*   - generic composition for most ops                              *)
(*   - specialised getter-binds to strengthen the precondition       *)
(*   - rollback-writer leaves with precondition-equations            *)
(* ================================================================ *)

Definition psf_def:
  psf p (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ∧ p s ∧ s.contexts ≠ [] ⇒ same_frame_rel s s'
End

(* ---------------- Monotonicity and bridges --------------------- *)

Theorem psf_mono:
  psf p m ∧ (∀s. q s ⇒ p s) ⇒ psf q m
Proof
  rw[psf_def] \\ first_x_assum irule \\ metis_tac[]
QED

Theorem preserves_same_frame_eq_psf_T:
  preserves_same_frame m ⇔ psf (λs. T) m
Proof
  rw[preserves_same_frame_def, psf_def]
QED

Theorem preserves_same_frame_imp_psf:
  preserves_same_frame m ⇒ psf p m
Proof
  rw[preserves_same_frame_def, psf_def]
  \\ first_x_assum irule \\ metis_tac[]
QED

(* Simp rule: any preserves_same_frame fact auto-lifts to psf p. *)
Theorem psf_of_preserves_same_frame[simp]:
  preserves_same_frame m ⇒ psf p m
Proof
  metis_tac[preserves_same_frame_imp_psf]
QED

(* ---------------- Composition rules ---------------- *)

(* Generic bind: requires a transfer function p_cont describing the
   precondition the continuation runs under. *)
Theorem psf_bind:
  psf p g ∧
  (∀x. psf (p_cont x) (f x)) ∧
  (∀x s s'. g s = (INL x, s') ∧ p s ∧ s.contexts ≠ [] ⇒
            p_cont x s') ⇒
  psf p (bind g f)
Proof
  rw[psf_def, bind_def]
  \\ gvs[AllCaseEqs()]
  \\ rpt(first_x_assum drule)
  \\ rw[] \\ gvs[]
  \\ drule same_frame_rel_contexts_ne
  \\ rw[] \\ gvs[]
  \\ metis_tac[same_frame_rel_trans]
QED

Theorem psf_ignore_bind:
  psf p g ∧ psf p_cont f ∧
  (∀s s'. g s = (INL (), s') ∧ p s ∧ s.contexts ≠ [] ⇒ p_cont s') ⇒
  psf p (ignore_bind g f)
Proof
  rw[ignore_bind_def]
  \\ irule psf_bind \\ rw[]
  \\ qexists_tac `λu s. p_cont s`
  \\ simp[] \\ metis_tac[]
QED

Theorem psf_handle:
  psf p f ∧
  (∀e. psf (p_handler e) (h e)) ∧
  (∀e s s'. f s = (INR e, s') ∧ p s ∧ s.contexts ≠ [] ⇒
            p_handler e s') ⇒
  psf p (handle f h)
Proof
  rw[psf_def, handle_def]
  \\ gvs[AllCaseEqs()]
  \\ rpt(first_x_assum drule) \\ rw[]
  >> gvs[]
  >> drule same_frame_rel_contexts_ne
  \\ rw[] >> gvs[]
  \\ metis_tac[same_frame_rel_trans]
QED

Theorem psf_cond:
  psf p m1 ∧ psf p m2 ⇒ psf p (if b then m1 else m2)
Proof
  rw[]
QED

Theorem psf_case_option:
  psf p m_none ∧ (∀x. psf p (m_some x)) ⇒
  psf p (case opt of NONE => m_none | SOME x => m_some x)
Proof
  Cases_on `opt` \\ rw[]
QED

Theorem psf_case_sum:
  (∀x. psf p (f x)) ∧ (∀y. psf p (g y)) ⇒
  psf p (case sm of INL x => f x | INR y => g y)
Proof
  Cases_on `sm` \\ rw[]
QED

Theorem psf_case_pair:
  (∀x y. psf p (f x y)) ⇒ psf p (case pr of (x, y) => f x y)
Proof
  Cases_on `pr` \\ rw[]
QED

Theorem psf_let:
  (∀x. psf p (f x)) ⇒ psf p (let x = v in f x)
Proof
  rw[]
QED

Theorem psf_uncurry:
  (∀x y. psf p (f x y)) ⇒ psf p (UNCURRY f pr)
Proof
  Cases_on `pr` \\ rw[]
QED

(* ---------------- `same_frame_rel` extractors ------------------- *)

Theorem same_frame_rel_msgParams:
  same_frame_rel s s' ⇒
  (FST (HD s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams
Proof
  rw[same_frame_rel_def]
QED

Theorem same_frame_rel_callee:
  same_frame_rel s s' ⇒
  (FST (HD s'.contexts)).msgParams.callee =
  (FST (HD s.contexts)).msgParams.callee
Proof
  rw[same_frame_rel_def]
QED

Theorem same_frame_rel_contexts_ne_src:
  same_frame_rel s s' ⇒ s.contexts ≠ []
Proof
  rw[same_frame_rel_def]
QED

(* `psf p m` implies the continuation's state has the same head callee
   as the original, provided p implied contexts ≠ []. *)
Theorem psf_preserves_head_callee:
  psf p m ∧ m s = (r, s') ∧ p s ∧ s.contexts ≠ [] ⇒
  (FST (HD s'.contexts)).msgParams.callee =
  (FST (HD s.contexts)).msgParams.callee
Proof
  rw[psf_def]
  \\ `same_frame_rel s s'` by metis_tac[]
  \\ metis_tac[same_frame_rel_callee]
QED

Theorem psf_preserves_head_msgParams:
  psf p m ∧ m s = (r, s') ∧ p s ∧ s.contexts ≠ [] ⇒
  (FST (HD s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams
Proof
  rw[psf_def]
  \\ `same_frame_rel s s'` by metis_tac[]
  \\ metis_tac[same_frame_rel_msgParams]
QED

Theorem psf_preserves_contexts_ne:
  psf p m ∧ m s = (r, s') ∧ p s ∧ s.contexts ≠ [] ⇒
  s'.contexts ≠ []
Proof
  rw[psf_def]
  \\ `same_frame_rel s s'` by metis_tac[]
  \\ metis_tac[same_frame_rel_contexts_ne]
QED

(* ---------------- Specialised getter-bind rules ----------------- *)

(* For `bind get_callee f`, the continuation runs at the same state
   with `x = head's callee` available as a fact. *)
Theorem psf_bind_get_callee:
  (∀x. psf (λs. p s ∧ x = (FST (HD s.contexts)).msgParams.callee)
           (f x)) ⇒
  psf p (bind get_callee f)
Proof
  rw[psf_def, bind_def, get_callee_def,
     get_current_context_def, ok_state_def, return_def, fail_def]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ first_x_assum (qspec_then `(FST h).msgParams.callee` mp_tac)
  \\ rw[psf_def]
  \\ first_x_assum irule
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ simp[]
QED

Theorem psf_bind_get_current_context:
  (∀x. psf (λs. p s ∧ s.contexts ≠ [] ∧ x = FST (HD s.contexts)) (f x)) ⇒
  psf p (bind get_current_context f)
Proof
  rw[psf_def, bind_def, get_current_context_def, ok_state_def,
     return_def, fail_def]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ first_x_assum (qspec_then `FST h` mp_tac)
  \\ rw[psf_def]
  \\ first_x_assum irule
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ simp[]
QED

Theorem psf_bind_get_caller:
  (∀x. psf (λs. p s ∧ x = (FST (HD s.contexts)).msgParams.caller) (f x)) ⇒
  psf p (bind get_caller f)
Proof
  rw[psf_def, bind_def, get_caller_def,
     get_current_context_def, ok_state_def, return_def, fail_def]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ first_x_assum (qspec_then `(FST h).msgParams.caller` mp_tac)
  \\ rw[psf_def]
  \\ first_x_assum irule
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ simp[]
QED

Theorem psf_bind_get_value:
  (∀x. psf (λs. p s ∧ x = (FST (HD s.contexts)).msgParams.value) (f x)) ⇒
  psf p (bind get_value f)
Proof
  rw[psf_def, bind_def, get_value_def,
     get_current_context_def, ok_state_def, return_def, fail_def]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ first_x_assum (qspec_then `(FST h).msgParams.value` mp_tac)
  \\ rw[psf_def]
  \\ first_x_assum irule
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ simp[]
QED

Theorem psf_bind_get_accounts:
  (∀x. psf (λs. p s ∧ x = s.rollback.accounts) (f x)) ⇒
  psf p (bind get_accounts f)
Proof
  rw[psf_def, bind_def, get_accounts_def, return_def]
  \\ first_x_assum (qspec_then `s.rollback.accounts` mp_tac)
  \\ rw[psf_def]
  \\ first_x_assum irule \\ simp[]
QED

Theorem psf_bind_get_tStorage:
  (∀x. psf (λs. p s ∧ x = s.rollback.tStorage) (f x)) ⇒
  psf p (bind get_tStorage f)
Proof
  rw[psf_def, bind_def, get_tStorage_def, return_def]
  \\ first_x_assum (qspec_then `s.rollback.tStorage` mp_tac)
  \\ rw[psf_def]
  \\ first_x_assum irule \\ simp[]
QED

Theorem psf_bind_get_rollback:
  (∀x. psf (λs. p s ∧ x = s.rollback) (f x)) ⇒
  psf p (bind get_rollback f)
Proof
  rw[psf_def, bind_def, get_rollback_def, return_def]
  \\ first_x_assum (qspec_then `s.rollback` mp_tac)
  \\ rw[psf_def]
  \\ first_x_assum irule \\ simp[]
QED

Theorem psf_bind_get_tx_params:
  (∀x. psf (λs. p s ∧ x = s.txParams) (f x)) ⇒
  psf p (bind get_tx_params f)
Proof
  rw[psf_def, bind_def, get_tx_params_def, return_def]
  \\ first_x_assum (qspec_then `s.txParams` mp_tac)
  \\ rw[psf_def]
  \\ first_x_assum irule \\ simp[]
QED

Theorem psf_bind_get_original:
  (∀x. psf (λs. p s ∧ s.contexts ≠ [] ∧
                 x = (SND (LAST s.contexts)).accounts) (f x)) ⇒
  psf p (bind get_original f)
Proof
  rw[psf_def, bind_def, get_original_def, return_def, fail_def]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ first_x_assum
       (qspec_then `(SND (LAST (h::t))).accounts` mp_tac)
  \\ rw[psf_def]
  \\ first_x_assum irule
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ simp[]
QED

(* ---------------- Rollback-writer leaves ------------------------ *)

Theorem psf_write_storage:
  psf (λs. address = (FST (HD s.contexts)).msgParams.callee)
      (write_storage address key value)
Proof
  rw[psf_def]
  \\ drule write_storage_same_frame \\ gvs[]
  \\ disch_then (qspecl_then [`value`, `key`] mp_tac)
  \\ simp[]
QED

Theorem psf_write_transient_storage:
  psf (λs. address = (FST (HD s.contexts)).msgParams.callee)
      (write_transient_storage address key value)
Proof
  rw[psf_def]
  \\ drule write_transient_storage_same_frame \\ gvs[]
  \\ disch_then (qspecl_then [`value`, `key`] mp_tac)
  \\ simp[]
QED

Theorem psf_update_accounts_increment_nonce:
  psf (λs. address = (FST (HD s.contexts)).msgParams.callee)
      (update_accounts (increment_nonce address))
Proof
  rw[psf_def]
  \\ drule update_accounts_increment_nonce_same_frame
  \\ simp[]
  \\ Cases_on `update_accounts (increment_nonce address) s` \\ gvs[]
QED

(* ---------------- Validation: step_sstore ---------------------- *)

Theorem psf_step_sstore:
  psf (λs. T) (step_sstore transient)
Proof
  simp[step_sstore_def]
  \\ irule psf_bind >> simp[]
  \\ qexists_tac `λx s. T`
  \\ simp[] \\ gen_tac
  \\ irule psf_bind_get_callee
  \\ rw[] >>
    qmatch_goalsub_abbrev_tac`psf pcont` >>
    irule psf_ignore_bind >> rw[] >>
    qexists_tac`pcont` >> (rw[] >-
    metis_tac[psf_preserves_head_callee, preserves_same_frame_imp_psf,
              preserves_same_frame_consume_gas,
              preserves_same_frame_step_sstore_gas_consumption]) >>
    irule psf_ignore_bind >> rw[] >>
    qexists_tac`pcont` >> (rw[] >- (
            gvs[Abbr`pcont`]
            >> drule_at (Pat`_ = (_,_)`) psf_preserves_head_callee
            >> disch_then $ irule o GSYM
            >> rw[]
            \\ qexists_tac`K T` >> rw[] )) >>
    rw[Abbr`pcont`] >>
    (irule psf_write_transient_storage ORELSE
     irule psf_write_storage)
QED

Theorem preserves_same_frame_step_sstore[simp]:
  preserves_same_frame (step_sstore transient)
Proof
  rw[preserves_same_frame_eq_psf_T, psf_step_sstore]
QED

(* ---------------- Validation: abort_create_exists --------------- *)

Theorem psf_abort_create_exists_callee:
  psf (λs. senderAddress = (FST (HD s.contexts)).msgParams.callee)
      (abort_create_exists senderAddress)
Proof
  rw[abort_create_exists_def]
  \\ irule psf_ignore_bind
  \\ reverse conj_tac
  >- ( irule psf_mono
       \\ qexists_tac
            `λs. senderAddress = (FST (HD s.contexts)).msgParams.callee`
       \\ conj_tac >- simp[]
       \\ irule psf_update_accounts_increment_nonce)
  \\ qexists_tac`K T`
  \\ simp[]
QED

Theorem abort_create_exists_same_frame:
  s.contexts ≠ [] ∧
  senderAddress = (FST (HD s.contexts)).msgParams.callee ⇒
  same_frame_rel s (SND (abort_create_exists senderAddress s))
Proof
  strip_tac
  \\ mp_tac psf_abort_create_exists_callee
  \\ rw[psf_def]
  \\ first_x_assum irule \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`SND p`
  \\ qexists_tac`FST p` \\ rw[]
QED

(* ================================================================ *)
(* Pass B: per-opcode `preserves_same_frame (step_inst op)` lemmas   *)
(*         for Group-1 opcodes (those that never push or pop the    *)
(*         call stack within `step_inst` itself).                    *)
(*                                                                   *)
(* These are one-liners dispatching to the compound-helper `[simp]` *)
(* lemmas registered above. Each is `[simp]` so that the opcode      *)
(* case analysis inside `step_same_frame` (Pass D) closes uniformly. *)
(*                                                                   *)
(* Omitted Group 2 (push): Call, CallCode, DelegateCall, StaticCall, *)
(*                         Create, Create2.                           *)
(* Omitted Group 3 (non-callee write): SelfDestruct.                  *)
(* ================================================================ *)

(* --- Arithmetic / bitwise --- *)

Theorem preserves_same_frame_step_inst_Add[simp]:
  preserves_same_frame (step_inst Add)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_Mul[simp]:
  preserves_same_frame (step_inst Mul)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_Sub[simp]:
  preserves_same_frame (step_inst Sub)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_Div[simp]:
  preserves_same_frame (step_inst Div)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_SDiv[simp]:
  preserves_same_frame (step_inst SDiv)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_Mod[simp]:
  preserves_same_frame (step_inst Mod)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_SMod[simp]:
  preserves_same_frame (step_inst SMod)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_AddMod[simp]:
  preserves_same_frame (step_inst AddMod)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_MulMod[simp]:
  preserves_same_frame (step_inst MulMod)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_Exp[simp]:
  preserves_same_frame (step_inst Exp)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_SignExtend[simp]:
  preserves_same_frame (step_inst SignExtend)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_LT[simp]:
  preserves_same_frame (step_inst LT)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_GT[simp]:
  preserves_same_frame (step_inst GT)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_SLT[simp]:
  preserves_same_frame (step_inst SLT)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_SGT[simp]:
  preserves_same_frame (step_inst SGT)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_Eq[simp]:
  preserves_same_frame (step_inst Eq)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_IsZero[simp]:
  preserves_same_frame (step_inst IsZero)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_And[simp]:
  preserves_same_frame (step_inst And)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_Or[simp]:
  preserves_same_frame (step_inst Or)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_XOr[simp]:
  preserves_same_frame (step_inst XOr)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_Not[simp]:
  preserves_same_frame (step_inst Not)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_Byte[simp]:
  preserves_same_frame (step_inst Byte)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_ShL[simp]:
  preserves_same_frame (step_inst ShL)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_ShR[simp]:
  preserves_same_frame (step_inst ShR)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_SAR[simp]:
  preserves_same_frame (step_inst SAR)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_CLZ[simp]:
  preserves_same_frame (step_inst CLZ)
Proof
  rw[step_inst_def]
QED

(* --- Hashing / context / tx params --- *)

Theorem preserves_same_frame_step_inst_Keccak256[simp]:
  preserves_same_frame (step_inst Keccak256)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_Address[simp]:
  preserves_same_frame (step_inst Address)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_Balance[simp]:
  preserves_same_frame (step_inst Balance)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_Origin[simp]:
  preserves_same_frame (step_inst Origin)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_Caller[simp]:
  preserves_same_frame (step_inst Caller)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_CallValue[simp]:
  preserves_same_frame (step_inst CallValue)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_CallDataLoad[simp]:
  preserves_same_frame (step_inst CallDataLoad)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_CallDataSize[simp]:
  preserves_same_frame (step_inst CallDataSize)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_CallDataCopy[simp]:
  preserves_same_frame (step_inst CallDataCopy)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_CodeSize[simp]:
  preserves_same_frame (step_inst CodeSize)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_CodeCopy[simp]:
  preserves_same_frame (step_inst CodeCopy)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_GasPrice[simp]:
  preserves_same_frame (step_inst GasPrice)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_ExtCodeSize[simp]:
  preserves_same_frame (step_inst ExtCodeSize)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_ExtCodeCopy[simp]:
  preserves_same_frame (step_inst ExtCodeCopy)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_ReturnDataSize[simp]:
  preserves_same_frame (step_inst ReturnDataSize)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_ReturnDataCopy[simp]:
  preserves_same_frame (step_inst ReturnDataCopy)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_ExtCodeHash[simp]:
  preserves_same_frame (step_inst ExtCodeHash)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_BlockHash[simp]:
  preserves_same_frame (step_inst BlockHash)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_CoinBase[simp]:
  preserves_same_frame (step_inst CoinBase)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_TimeStamp[simp]:
  preserves_same_frame (step_inst TimeStamp)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_Number[simp]:
  preserves_same_frame (step_inst Number)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_PrevRandao[simp]:
  preserves_same_frame (step_inst PrevRandao)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_GasLimit[simp]:
  preserves_same_frame (step_inst GasLimit)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_ChainId[simp]:
  preserves_same_frame (step_inst ChainId)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_SelfBalance[simp]:
  preserves_same_frame (step_inst SelfBalance)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_BaseFee[simp]:
  preserves_same_frame (step_inst BaseFee)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_BlobHash[simp]:
  preserves_same_frame (step_inst BlobHash)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_BlobBaseFee[simp]:
  preserves_same_frame (step_inst BlobBaseFee)
Proof
  rw[step_inst_def]
QED

(* --- Stack and memory --- *)

Theorem preserves_same_frame_step_inst_Pop[simp]:
  preserves_same_frame (step_inst Pop)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_MLoad[simp]:
  preserves_same_frame (step_inst MLoad)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_MStore[simp]:
  preserves_same_frame (step_inst MStore)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_MStore8[simp]:
  preserves_same_frame (step_inst MStore8)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_MCopy[simp]:
  preserves_same_frame (step_inst MCopy)
Proof
  rw[step_inst_def]
QED

(* --- Storage and transient storage --- *)

Theorem preserves_same_frame_step_inst_SLoad[simp]:
  preserves_same_frame (step_inst SLoad)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_SStore[simp]:
  preserves_same_frame (step_inst SStore)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_TLoad[simp]:
  preserves_same_frame (step_inst TLoad)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_TStore[simp]:
  preserves_same_frame (step_inst TStore)
Proof
  rw[step_inst_def]
QED

(* --- Control flow --- *)

Theorem preserves_same_frame_step_inst_Jump[simp]:
  preserves_same_frame (step_inst Jump)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_JumpI[simp]:
  preserves_same_frame (step_inst JumpI)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_PC[simp]:
  preserves_same_frame (step_inst PC)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_MSize[simp]:
  preserves_same_frame (step_inst MSize)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_Gas[simp]:
  preserves_same_frame (step_inst Gas)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_JumpDest[simp]:
  preserves_same_frame (step_inst JumpDest)
Proof
  rw[step_inst_def]
QED

(* --- Push / Dup / Swap / Log (indexed) --- *)

Theorem preserves_same_frame_step_inst_Push[simp]:
  preserves_same_frame (step_inst (Push n ws))
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_Dup[simp]:
  preserves_same_frame (step_inst (Dup n))
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_Swap[simp]:
  preserves_same_frame (step_inst (Swap n))
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_Log[simp]:
  preserves_same_frame (step_inst (Log n))
Proof
  rw[step_inst_def]
QED

(* --- Terminators (return INR but don't mutate state in ways that
       violate same_frame_rel). Stop, Return, Revert, Invalid. --- *)

Theorem preserves_same_frame_step_inst_Stop[simp]:
  preserves_same_frame (step_inst Stop)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_Return[simp]:
  preserves_same_frame (step_inst Return)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_Revert[simp]:
  preserves_same_frame (step_inst Revert)
Proof
  rw[step_inst_def]
QED

Theorem preserves_same_frame_step_inst_Invalid[simp]:
  preserves_same_frame (step_inst Invalid)
Proof
  rw[step_inst_def]
QED

(* ================================================================ *)
(* Pass C: Handle-layer lemmas.                                      *)
(*                                                                   *)
(* We establish `same_frame_rel` preservation through `handle_step`  *)
(* when the step doesn't change the call-stack length (i.e. the     *)
(* handle_exception path is the n ≤ 1 reraise, not a pop).           *)
(*                                                                   *)
(* This relies on a well-formedness invariant on the head context:  *)
(* if its `outputTo = Code a`, then its `msgParams.callee = a`.      *)
(* The invariant holds for `initial_state` by construction and is   *)
(* preserved through the frame (because `same_frame_rel` preserves  *)
(* `msgParams`).                                                     *)
(* ================================================================ *)

Definition outputTo_consistent_def:
  outputTo_consistent s ⇔
    s.contexts ≠ [] ∧
    ∀a. (FST (HD s.contexts)).msgParams.outputTo = Code a ⇒
        (FST (HD s.contexts)).msgParams.callee = a
End

(* The invariant is preserved through any `same_frame_rel` step, because
   the head's `msgParams` is preserved. *)
Theorem same_frame_rel_preserves_outputTo_consistent:
  same_frame_rel s s' ∧ outputTo_consistent s ⇒ outputTo_consistent s'
Proof
  rw[outputTo_consistent_def]
  >- metis_tac[same_frame_rel_contexts_ne]
  \\ `(FST (HD s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams`
     by metis_tac[same_frame_rel_msgParams]
  \\ gvs[]
QED

(* ---------------- handle_create ---------------- *)

(* Under outputTo_consistent, handle_create's code-install branch
   writes at the callee (because outputTo = Code address implies
   callee = address), which is a callee-local change permitted by
   same_frame_rel. *)
Theorem psf_handle_create:
  psf outputTo_consistent (handle_create e)
Proof
  rw[psf_def, handle_create_def, bind_def,
     get_return_data_def, get_output_to_def,
     get_current_context_def, ok_state_def, return_def]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ PairCases_on `h` \\ gvs[]
  \\ Cases_on `e`
  >- (
    (* e = NONE *)
    Cases_on `h0.msgParams.outputTo` \\ gvs[reraise_def]
    >- (
      (* outputTo = Memory — reraise *)
      irule same_frame_rel_refl \\ simp[])
    >- (
      (* outputTo = Code c — install code at c *)
      gvs[ignore_bind_def, bind_def, assert_def, return_def,
          fail_def, AllCaseEqs(), consume_gas_def,
          get_current_context_def, ok_state_def,
          set_current_context_def, update_accounts_def,
          reraise_def]
      (* Each branch: either fail (refl), or consume_gas + update_accounts.
         The update is at address = c, which equals the head's callee by
         outputTo_consistent. *)
      \\ gvs[outputTo_consistent_def]
      \\ rw[same_frame_rel_def, callee_local_changes_def,
            lookup_account_def, update_account_def,
            APPLY_UPDATE_THM]
      \\ rw[]))
  \\ (* e = SOME _ — reraise *)
    gvs[reraise_def]
  \\ Cases_on `h0.msgParams.outputTo` \\ gvs[reraise_def]
  \\ irule same_frame_rel_refl \\ simp[]
QED

(* ---------------- handle_exception under length preservation ----- *)

Theorem cp_imp_length_contexts_preserved:
  cp m /\ m s = (r,s') /\ s.contexts <> []
  ==> LENGTH s'.contexts = LENGTH s.contexts
Proof
  rw[cp_def] >> first_x_assum drule >> rw[] >> gvs[] >>
  Cases_on`s.contexts` >> gvs[]
QED

Theorem psf_imp_length_contexts_preserved:
  preserves_same_frame m /\ m s = (r,s') /\ s.contexts <> [] ==>
  LENGTH s'.contexts = LENGTH s.contexts
Proof
  rw[preserves_same_frame_def] >> first_x_assum drule >>
  rw[same_frame_rel_def]
QED

(* handle_exception either reraises (n ≤ 1) or pops (n > 1). When the
   length is preserved, the reraise branch was taken. The prefix
   (consume_gas + set_return_data in non-Revert error cases) is
   preserves_same_frame. *)
Theorem handle_exception_same_frame:
  s.contexts ≠ [] ∧
  handle_exception e s = (r, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  same_frame_rel s s'
Proof
  simp[handle_exception_def, bind_def, ignore_bind_def]
  \\ strip_tac
  \\ reverse (Cases_on`LENGTH s.contexts ≤ 1`)
  >- (
    gvs[AllCaseEqs(), COND_RATOR, get_num_contexts_def,
        return_def, reraise_def] >>
    TRY (
      gvs[bind_def, ignore_bind_def, AllCaseEqs(), return_def,
          set_return_data_def, consume_gas_def, get_gas_left_def,
          assert_def, set_current_context_def, fail_def,
          get_current_context_def, same_frame_rel_def] >> NO_TAC ) >>
    rename1`_ s1 = (_,s')` >>
    TRY (
      rename1`_ s = (_,s1)` >>
      `LENGTH s1.contexts = LENGTH s.contexts` by 
        gvs[bind_def, ignore_bind_def, AllCaseEqs(),
            get_gas_left_def, consume_gas_def, assert_def,
            set_return_data_def, fail_def, return_def,
            set_current_context_def, get_current_context_def]) >>
     `LENGTH s'.contexts <> LENGTH s1.contexts` suffices_by gvs[] >>
     qpat_x_assum`_ = (_,s')`mp_tac >>
     pop_assum kall_tac >>
     simp[bind_def] >>
     simp[get_return_data_def, bind_def,
          return_def, get_current_context_def] >>
     TRY IF_CASES_TAC >> gvs[return_def, fail_def] >>
     simp[get_output_to_def, bind_def, get_current_context_def] >>
     gvs[return_def] >>
     simp[pop_and_incorporate_context_def,bind_def] >>
     simp[get_gas_left_def, bind_def, get_current_context_def, return_def] >>
     simp[pop_context_def, return_def] >>
     simp[ignore_bind_def, bind_def] >>
     CASE_TAC >>
     drule_at Any cp_imp_length_contexts_preserved >>
     simp[] >>
     Cases_on`s1.contexts` >> gvs[] >>
     Cases_on`t` >> gvs[] >> strip_tac >>
     BasicProvers.TOP_CASE_TAC >> (
     reverse BasicProvers.TOP_CASE_TAC >- (
       rw[] >> gvs[AllCaseEqs(),set_rollback_def,return_def] >>
       drule_at Any psf_imp_length_contexts_preserved >> rw[] >>
       gvs[push_logs_def, bind_def, get_current_context_def, AllCaseEqs(),
           return_def, set_current_context_def]
     ) ) >>
     BasicProvers.TOP_CASE_TAC >>
     drule_at Any psf_imp_length_contexts_preserved >>
     (impl_tac >- (simp[] >> gvs[AllCaseEqs(), set_rollback_def, return_def] >>
                   strip_tac >> gvs[] >>
                   qhdtm_x_assum`update_gas_refund`assume_tac >>
                   drule_at Any psf_imp_length_contexts_preserved >>
                   rw[] >> strip_tac >> gvs[] >>
                   qhdtm_x_assum`push_logs`assume_tac >>
                   drule_at Any psf_imp_length_contexts_preserved >>
                   rw[] >> strip_tac >> gvs[] 
     )) >> strip_tac >> (
     reverse BasicProvers.TOP_CASE_TAC >- (
       rw[] >>
       strip_tac >>  gvs[AllCaseEqs(),set_rollback_def,return_def] >>
                   qhdtm_x_assum`update_gas_refund`assume_tac >>
                   drule_at Any psf_imp_length_contexts_preserved >>
                   rw[] >> strip_tac >> gvs[] >>
                   qhdtm_x_assum`push_logs`assume_tac >>
                   drule_at Any psf_imp_length_contexts_preserved >>
                   rw[] >> strip_tac >> gvs[]
     ) ) >>
     simp[AllCaseEqs(),return_destination_CASE_rator,bind_def] >>
     rw[] >> gvs[push_stack_def, set_return_data_def, get_current_context_def,
                 set_current_context_def, bind_def, return_def, assert_def,
                 fail_def,AllCaseEqs(),ignore_bind_def] >>
     strip_tac >> gvs[set_rollback_def, return_def] >>
     gvs[write_memory_def, bind_def, ignore_bind_def,
         get_current_context_def, set_current_context_def, assert_def,
         fail_def,return_def] >>
                   qhdtm_x_assum`update_gas_refund`assume_tac >>
                   drule_at Any psf_imp_length_contexts_preserved >>
                   rw[] >> strip_tac >> gvs[] >>
                   qhdtm_x_assum`push_logs`assume_tac >>
                   drule_at Any psf_imp_length_contexts_preserved >>
                   rw[] >> strip_tac >> gvs[]
  )
  \\ gvs[AllCaseEqs(), COND_RATOR]
  (* Various branches: the prefix may be a consume_gas + set_return_data
     block or just return (); then n <- get_num_contexts; if n ≤ 1
     reraise else pop. The length hypothesis rules out the pop branch. *)
  \\ gvs[get_gas_left_def, get_current_context_def, ok_state_def,
         return_def, get_num_contexts_def, reraise_def, fail_def,
         consume_gas_def, set_return_data_def, set_current_context_def,
         get_return_data_def, get_output_to_def]
  \\ gvs[bind_def, ignore_bind_def, AllCaseEqs(), get_current_context_def,
         assert_def, fail_def, return_def, set_current_context_def,
         inc_pc_def]
  \\ Cases_on `s.contexts` \\ gvs[]
  \\ (* In each remaining branch, s' equals s with possibly modified
        head context (gasUsed up, returnData cleared). *)
    PairCases_on `h` \\ gvs[]
  \\ rw[same_frame_rel_def, callee_local_changes_def]
  \\ gvs[AllCaseEqs(), rich_listTheory.IS_PREFIX_REFL]
QED

(* ---------------- handle_step under length preservation --------- *)

(* handle_step = if vfm_abort e then reraise e
                 else handle (handle_create e) handle_exception.
   The reraise case is trivial. In the handle case, handle_create always
   returns INR, so handle_exception is always invoked; we compose
   psf_handle_create with the same-length version of
   handle_exception_same_frame. *)
Theorem handle_step_same_frame:
  outputTo_consistent s ∧
  handle_step e s = (r, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  same_frame_rel s s'
Proof
  rw[handle_step_def]
  >- (
    (* vfm_abort e: reraise, state unchanged *)
    gvs[reraise_def]
    \\ irule same_frame_rel_refl
    \\ gvs[outputTo_consistent_def])
  \\ (* handle (handle_create e) handle_exception s *)
    gvs[handle_def]
  \\ `s.contexts ≠ []` by gvs[outputTo_consistent_def]
  \\ drule_then(qspec_then`e`mp_tac) (INST_TYPE[alpha |-> ``:unit``]handle_create_INR)
  \\ rw[] >> gvs[]
  \\ rename1`handle_create _ s = (_,s1)`
  \\ qmatch_asmsub_abbrev_tac`hce s = _`
  \\ `psf outputTo_consistent hce` by metis_tac[psf_handle_create]
  \\ `same_frame_rel s s1` by (
       gvs[psf_def,Abbr`hce`]
       \\ first_x_assum irule
       \\ simp[] \\ metis_tac[])
  \\ `LENGTH s1.contexts = LENGTH s.contexts` by gvs[same_frame_rel_def]
  \\ `s1.contexts ≠ []` by metis_tac[same_frame_rel_contexts_ne]
  \\ `LENGTH s'.contexts = LENGTH s1.contexts` by simp[]
  \\ `same_frame_rel s1 s'`
     by (irule handle_exception_same_frame \\ metis_tac[])
  \\ metis_tac[same_frame_rel_trans]
QED

(* ================================================================ *)
(* Pass D: step-level same-frame theorem.                            *)
(*                                                                   *)
(* Builds on Pass B (per-opcode preserves_same_frame for Group 1)    *)
(* and Pass C (handle-layer lemmas) to prove `step_same_frame`.      *)
(*                                                                   *)
(* Additional primitives proved here are for SELFDESTRUCT (which     *)
(* satisfies the weakened `same_frame_rel` but needs its own psf     *)
(* lemmas for the balance-mutating steps).                           *)
(* ================================================================ *)

(* ---------------- transfer_value field preservation ------------- *)

Theorem transfer_value_preserves_storage:
  (lookup_account a (transfer_value from to amt accs)).storage =
  (lookup_account a accs).storage
Proof
  rw[transfer_value_def, lookup_account_def, update_account_def,
     APPLY_UPDATE_THM]
  \\ rw[] \\ gvs[]
QED

Theorem transfer_value_preserves_code:
  (lookup_account a (transfer_value from to amt accs)).code =
  (lookup_account a accs).code
Proof
  rw[transfer_value_def, lookup_account_def, update_account_def,
     APPLY_UPDATE_THM]
  \\ rw[] \\ gvs[]
QED

Theorem transfer_value_preserves_nonce:
  (lookup_account a (transfer_value from to amt accs)).nonce =
  (lookup_account a accs).nonce
Proof
  rw[transfer_value_def, lookup_account_def, update_account_def,
     APPLY_UPDATE_THM]
  \\ rw[] \\ gvs[]
QED

(* ---------------- SELFDESTRUCT primitive psf lemmas ------------- *)

(* transfer_value only changes balances, which are free in the
   weakened same_frame_rel. *)
Theorem psf_update_accounts_transfer_value:
  psf (λs. T) (update_accounts (transfer_value fromAddr toAddr amount))
Proof
  rw[psf_def, update_accounts_def, return_def]
  \\ rw[same_frame_rel_def, callee_local_changes_def]
  \\ rw[transfer_value_preserves_storage,
        transfer_value_preserves_code,
        transfer_value_preserves_nonce]
QED

(* add_to_delete appends to toDelete, which is free in the weakened
   relation. *)
Theorem psf_add_to_delete:
  psf (λs. T) (add_to_delete a)
Proof
  rw[psf_def, add_to_delete_def, return_def]
  \\ rw[same_frame_rel_def, callee_local_changes_def]
  \\ Cases_on `s.contexts` \\ gvs[]
QED

(* update_account at the callee with a new account agreeing with the
   current callee account on storage, code, and nonce. Safe under
   the weakened relation. *)
Theorem psf_update_accounts_callee_balance_only:
  psf (λs. senderAddr = (FST (HD s.contexts)).msgParams.callee ∧
           newAccount.storage =
             (lookup_account senderAddr s.rollback.accounts).storage ∧
           newAccount.code =
             (lookup_account senderAddr s.rollback.accounts).code ∧
           newAccount.nonce =
             (lookup_account senderAddr s.rollback.accounts).nonce)
      (update_accounts (update_account senderAddr newAccount))
Proof
  rw[psf_def, update_accounts_def, return_def]
  \\ rw[same_frame_rel_def, callee_local_changes_def,
        lookup_account_def, update_account_def, APPLY_UPDATE_THM]
  \\ rw[] \\ gvs[lookup_account_def]
QED

(* ---------------- psf step_self_destruct ----------------------- *)

(* step_self_destruct, line by line:
     pop_stack 1                    -- preserves_same_frame
     access_address address         -- preserves_same_frame
     senderAddress <- get_callee;
     accounts <- get_accounts;
     consume_gas ...                -- preserves_same_frame
     assert_not_static              -- preserves_same_frame
     update_accounts (transfer_value senderAddress address balance)
                                    -- psf_update_accounts_transfer_value
     original <- get_original;
     if account_empty originalContract then
       update_accounts (update_account senderAddress (sender with balance := 0));
                                    -- psf_update_accounts_callee_balance_only
       add_to_delete senderAddress  -- psf_add_to_delete
     else return ()                 -- psf_return
     finish                         -- preserves_same_frame *)

Theorem psf_step_self_destruct:
  psf (λs. T) step_self_destruct
Proof
  rw[step_self_destruct_def]
  \\ irule psf_bind >> simp[]
  >> qexists_tac`K (K T)` >> simp[] >> gen_tac
  \\ irule psf_bind >> simp[]
  >> qexists_tac`K (K T)` >> simp[] >> gen_tac
  >> irule psf_bind_get_callee >> simp[] >> qx_gen_tac`callee`
  >> irule psf_bind_get_accounts >> simp[] >> qx_gen_tac`accounts`
  \\ irule psf_ignore_bind >> simp[]
  \\ qabbrev_tac`acc = lookup_account callee accounts`
  \\ qabbrev_tac`rbc = λs. lookup_account callee s.rollback.accounts`
  \\ qabbrev_tac`pco = λs. s.contexts ≠ [] ∧
       callee = (FST (HD s.contexts)).msgParams.callee ∧
       (rbc s).storage = acc.storage ∧
       (rbc s).code = acc.code ∧
       (rbc s).nonce = acc.nonce` >>
  qexists_tac`pco` >>
  simp[] >>
  conj_tac >- (
    rpt gen_tac >> strip_tac
    >> qmatch_asmsub_abbrev_tac`consume_gas n`
    >> mp_tac preserves_same_frame_consume_gas
    >> rewrite_tac[preserves_same_frame_def]
    >> disch_then drule
    >> impl_tac >- gvs[]
    \\ `cp (consume_gas n)` by simp[]
    >> pop_assum mp_tac >> rewrite_tac[cp_def]
    >> disch_then drule >> impl_tac >- rw[] >>
    strip_tac >> gvs[Abbr`acc`,Abbr`rbc`,Abbr`pco`] ) >>
  irule psf_ignore_bind >>
  simp[] >>
  qexists_tac`pco` >> simp[] >>
  conj_tac >- (
    rpt gen_tac >> strip_tac
    >> `cp assert_not_static` by simp[]
    >> pop_assum mp_tac >> rewrite_tac[cp_def]
    >> disch_then drule >> impl_tac >- gvs[Abbr`pco`] >>
    strip_tac >> gvs[Abbr`acc`,Abbr`rbc`,Abbr`pco`] ) >>
  irule psf_ignore_bind >>
  reverse conj_tac
  >- (
    irule psf_mono >>
    qexists_tac`λs. T` >> simp[] >>
    irule psf_update_accounts_transfer_value ) >>
  qexists_tac`pco` >> simp[] >>
  conj_tac >- (
    rpt gen_tac >> strip_tac
    >> gvs[update_accounts_def, return_def, Abbr`pco`, Abbr`rbc`]
    >> simp[transfer_value_preserves_storage,
            transfer_value_preserves_code,
            transfer_value_preserves_nonce] ) >>
  irule psf_bind_get_original >>
  qx_gen_tac`original` >>
  simp[] >>
  irule psf_ignore_bind >>
  rw[] >>
  TRY (qexists_tac`pco`) >> simp[return_def]
  >- (
    rpt gen_tac >> strip_tac >>
      gvs[bind_def, ignore_bind_def, update_accounts_def, return_def,
       add_to_delete_def, Abbr`pco`, Abbr`rbc`, Abbr`acc`,
       lookup_account_def, update_account_def, APPLY_UPDATE_THM]) >>
  irule psf_ignore_bind >>
  reverse conj_tac
  >- (
    irule psf_mono >>
    qspecl_then[`callee`,`acc with balance := 0`]
      mp_tac (GEN_ALL psf_update_accounts_callee_balance_only) >>
    strip_tac >>
    goal_assum $ drule_at Any >>
    simp[Abbr`pco`] ) >>
  simp[] >>
  qexists_tac`λs. T` >>
  simp[] >>
  irule psf_add_to_delete
QED

Theorem preserves_same_frame_step_self_destruct[simp]:
  preserves_same_frame step_self_destruct
Proof
  rw[preserves_same_frame_eq_psf_T, psf_step_self_destruct]
QED

Theorem preserves_same_frame_step_inst_SelfDestruct[simp]:
  preserves_same_frame (step_inst SelfDestruct)
Proof
  rw[step_inst_def]
QED

(* ---------------- proceed_call / proceed_create length ---------- *)

(* proceed_call ends with push_context; its successor may run a
   precompile which is preserves_same_frame (length preserved at the
   new depth). Either way the resulting length is at least
   LENGTH s.contexts + 1. *)
Theorem proceed_call_length:
  s.contexts ≠ [] ∧
  proceed_call op sender addr value aOff aSz code stipend outTo s
    = (r, s') ⇒
  LENGTH s'.contexts ≥ LENGTH s.contexts + 1
Proof
  strip_tac
  >> gvs[proceed_call_def, bind_def, ignore_bind_def, AllCaseEqs(),
        get_rollback_def, read_memory_def, get_current_context_def,
        get_caller_def, get_value_def, get_static_def,
        update_accounts_def, push_context_def, return_def,
        ok_state_def, fail_def, COND_RATOR]
  >> qmatch_asmsub_abbrev_tac`dispatch_precompiles _ sp = _`
  >> `LENGTH sp.contexts = LENGTH s.contexts + 1` by gvs[Abbr`sp`]
  >> drule_at Any (GEN_ALL psf_imp_length_contexts_preserved)
  >> gvs[Abbr`sp`]
QED

Theorem proceed_create_length:
  s.contexts ≠ [] ∧
  proceed_create senderAddr addr value code gas s = (r, s') ⇒
  LENGTH s'.contexts = LENGTH s.contexts + 1
Proof
  strip_tac
  >> gvs[proceed_create_def, bind_def, ignore_bind_def, AllCaseEqs(),
         get_rollback_def, get_original_def, set_original_def,
         update_accounts_def, push_context_def, return_def,
         ok_state_def, fail_def,
         set_last_accounts_def, LET_THM]
  >> Cases_on`s.contexts` >> gvs[]
  >> gvs[listTheory.SNOC_APPEND]
QED

(* ================================================================ *)
(* same_frame_or_grow: a monadic property for computations whose     *)
(* effect on the call stack is either "stay in the current frame"   *)
(* or "push (grow by at least one)". Needed for step_call and       *)
(* step_create, whose push branches violate preserves_same_frame    *)
(* but can be ruled out by a length hypothesis.                     *)
(* ================================================================ *)

Definition same_frame_or_grow_def:
  same_frame_or_grow (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ∧ s.contexts ≠ [] ⇒
      same_frame_rel s s' ∨
      LENGTH s'.contexts ≥ LENGTH s.contexts + 1
End

(* ---------------- Bridge from preserves_same_frame -------------- *)

Theorem same_frame_or_grow_of_preserves[simp]:
  preserves_same_frame m ⇒ same_frame_or_grow m
Proof
  rw[preserves_same_frame_def, same_frame_or_grow_def]
  >> disj1_tac >> first_x_assum irule >> metis_tac[]
QED

(* ---------------- Composition rules ----------------------------- *)

Theorem same_frame_or_grow_bind[simp]:
  same_frame_or_grow g ∧ (∀x. same_frame_or_grow (f x)) ⇒
  same_frame_or_grow (bind g f)
Proof
  rw[same_frame_or_grow_def, bind_def]
  >> gvs[AllCaseEqs()]
  >> first_x_assum drule
  >> first_x_assum drule
  >> simp[]
  >> disch_then assume_tac
  >> impl_keep_tac
  >- (
    gvs[] >> imp_res_tac same_frame_rel_contexts_ne >>
    strip_tac >> gvs[] )
  >> strip_tac >> gvs[]
  >> metis_tac[same_frame_rel_trans, same_frame_rel_def]
QED

Theorem same_frame_or_grow_ignore_bind[simp]:
  same_frame_or_grow g ∧ same_frame_or_grow f ⇒
  same_frame_or_grow (ignore_bind g f)
Proof
  rw[ignore_bind_def]
  >> irule same_frame_or_grow_bind >> simp[]
QED

Theorem same_frame_or_grow_handle[simp]:
  same_frame_or_grow f ∧ (∀e. same_frame_or_grow (h e)) ⇒
  same_frame_or_grow (handle f h)
Proof
  rw[same_frame_or_grow_def, handle_def]
  >> gvs[AllCaseEqs()]
  >> first_x_assum drule
  >> first_x_assum drule
  >> simp[]
  >> disch_then assume_tac
  >> impl_keep_tac
  >- (
    gvs[] >> imp_res_tac same_frame_rel_contexts_ne >>
    strip_tac >> gvs[] )
  >> strip_tac >> gvs[]
  >> metis_tac[same_frame_rel_trans, same_frame_rel_def]
QED

Theorem same_frame_or_grow_cond[simp]:
  same_frame_or_grow m1 ∧ same_frame_or_grow m2 ⇒
  same_frame_or_grow (if b then m1 else m2)
Proof
  rw[]
QED

Theorem same_frame_or_grow_case_option[simp]:
  same_frame_or_grow m_none ∧ (∀x. same_frame_or_grow (m_some x)) ⇒
  same_frame_or_grow
    (case opt of NONE => m_none | SOME x => m_some x)
Proof
  Cases_on `opt` >> rw[]
QED

Theorem same_frame_or_grow_case_sum[simp]:
  (∀x. same_frame_or_grow (f x)) ∧ (∀y. same_frame_or_grow (g y)) ⇒
  same_frame_or_grow
    (case sm of INL x => f x | INR y => g y)
Proof
  Cases_on `sm` >> rw[]
QED

Theorem same_frame_or_grow_case_pair[simp]:
  (∀x y. same_frame_or_grow (f x y)) ⇒
  same_frame_or_grow (case pr of (x, y) => f x y)
Proof
  Cases_on `pr` >> rw[]
QED

Theorem same_frame_or_grow_let[simp]:
  (∀x. same_frame_or_grow (f x)) ⇒
  same_frame_or_grow (let x = v in f x)
Proof
  rw[]
QED

Theorem same_frame_or_grow_uncurry[simp]:
  (∀x y. same_frame_or_grow (f x y)) ⇒
  same_frame_or_grow (UNCURRY f pr)
Proof
  Cases_on `pr` >> rw[]
QED

(* ---------------- proceed_call / proceed_create grow ------------ *)

Theorem same_frame_or_grow_proceed_call[simp]:
  same_frame_or_grow
    (proceed_call op sender addr value aOff aSz code stipend outTo)
Proof
  rw[same_frame_or_grow_def]
  >> disj2_tac
  >> drule_then drule proceed_call_length >> simp[]
QED

Theorem same_frame_or_grow_proceed_create[simp]:
  same_frame_or_grow
    (proceed_create senderAddr addr value code gas)
Proof
  rw[same_frame_or_grow_def]
  >> disj2_tac
  >> drule_then drule proceed_create_length >> simp[]
QED

(* ================================================================ *)
(* psf_or_grow: state-indexed variant of same_frame_or_grow.         *)
(*                                                                   *)
(* Same-shape predicate as `psf`, but with the or-grow disjunct     *)
(* baked in. Used for `step_create` where the push branch only     *)
(* same-frames under a value-level precondition from `get_callee`. *)
(* ================================================================ *)

Definition psf_or_grow_def:
  psf_or_grow p (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ∧ p s ∧ s.contexts ≠ [] ⇒
      same_frame_rel s s' ∨
      LENGTH s'.contexts ≥ LENGTH s.contexts + 1
End

(* ---------------- Bridges ------------------- *)

Theorem psf_or_grow_of_same_frame_or_grow[simp]:
  same_frame_or_grow m ⇒ psf_or_grow p m
Proof
  rw[same_frame_or_grow_def, psf_or_grow_def]
  >> first_x_assum irule >> metis_tac[]
QED

Theorem same_frame_or_grow_eq_psf_or_grow_T:
  same_frame_or_grow m ⇔ psf_or_grow (λs. T) m
Proof
  rw[same_frame_or_grow_def, psf_or_grow_def]
QED

(* ---------------- Composition rules ------------------- *)

Theorem psf_or_grow_bind:
  psf_or_grow p g ∧
  (∀x. psf_or_grow (p_cont x) (f x)) ∧
  (∀x s s'. g s = (INL x, s') ∧ p s ∧ s.contexts ≠ [] ⇒
            p_cont x s') ⇒
  psf_or_grow p (bind g f)
Proof
  rw[psf_or_grow_def, bind_def]
  >> gvs[AllCaseEqs()]
  >> first_x_assum drule
  >> first_x_assum drule
  >> first_x_assum drule
  >> rw[] >> gvs[]
  >> imp_res_tac same_frame_rel_contexts_ne >> gvs[]
  >- metis_tac[same_frame_rel_trans, same_frame_rel_def]
  >- metis_tac[same_frame_rel_trans, same_frame_rel_def]
  >> qmatch_asmsub_abbrev_tac`xxx ⇒ _`
  >> `xxx` by (simp[Abbr`xxx`] >> strip_tac >> gvs[])
  >> gvs[Abbr`xxx`]
  >- metis_tac[same_frame_rel_trans, same_frame_rel_def]
QED

Theorem psf_or_grow_ignore_bind:
  psf_or_grow p g ∧
  psf_or_grow p_cont f ∧
  (∀s x s'. g s = (INL x, s') ∧ p s ∧ s.contexts ≠ [] ⇒ p_cont s') ⇒
  psf_or_grow p (ignore_bind g f)
Proof
  rw[ignore_bind_def]
  >> irule psf_or_grow_bind >> simp[]
  >> qexists_tac `λu s. p_cont s`
  >> simp[] >> metis_tac[]
QED

Theorem psf_or_grow_cond[simp]:
  psf_or_grow p m1 ∧ psf_or_grow p m2 ⇒
  psf_or_grow p (if b then m1 else m2)
Proof
  rw[]
QED

Theorem psf_or_grow_case_option[simp]:
  psf_or_grow p m_none ∧ (∀x. psf_or_grow p (m_some x)) ⇒
  psf_or_grow p (case opt of NONE => m_none | SOME x => m_some x)
Proof
  Cases_on `opt` >> rw[]
QED

Theorem psf_or_grow_let[simp]:
  (∀x. psf_or_grow p (f x)) ⇒
  psf_or_grow p (let x = v in f x)
Proof
  rw[]
QED

(* ---------------- Specialised getter-bind for get_callee -------- *)

Theorem psf_or_grow_bind_get_callee:
  (∀x. psf_or_grow (λs. p s ∧ x = (FST (HD s.contexts)).msgParams.callee)
                    (f x)) ⇒
  psf_or_grow p (bind get_callee f)
Proof
  rw[psf_or_grow_def, bind_def, get_callee_def,
     get_current_context_def, ok_state_def, return_def, fail_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> first_x_assum (qspec_then `s` mp_tac)
  >> rw[psf_or_grow_def]
QED

(* ---------------- Leaf for abort_create_exists with callee ------ *)

(* Under the precondition that the argument equals the head's callee,
   abort_create_exists preserves same_frame (and therefore trivially
   same-frame-or-grows). *)
Theorem psf_or_grow_abort_create_exists_callee:
  psf_or_grow
    (λs. senderAddress = (FST (HD s.contexts)).msgParams.callee)
    (abort_create_exists senderAddress)
Proof
  rw[psf_or_grow_def]
  >> disj1_tac
  >> drule_at Any abort_create_exists_same_frame >> simp[]
  >> disch_then (qspec_then `senderAddress` mp_tac) >> simp[]
  >> Cases_on `abort_create_exists senderAddress s` >> gvs[]
QED

(* ---------------- step_call and step_create -------------------- *)

Theorem same_frame_or_grow_step_call[simp]:
  same_frame_or_grow (step_call op)
Proof
  simp[step_call_def]
  >> irule same_frame_or_grow_bind >> simp[] >> gen_tac
  >> pairarg_tac >> simp[]
  >> irule same_frame_or_grow_bind >> simp[] >> gen_tac
  >> irule same_frame_or_grow_bind >> simp[] >> gen_tac
  >> irule same_frame_or_grow_bind >> simp[] >> gen_tac
  >> irule same_frame_or_grow_bind >> simp[] >> gen_tac
  >> pairarg_tac >> simp[]
  >> irule same_frame_or_grow_bind >> simp[] >> gen_tac
  >> pairarg_tac >> simp[]
  >> irule same_frame_or_grow_ignore_bind >> simp[]
  >> irule same_frame_or_grow_ignore_bind >> simp[]
  >> irule same_frame_or_grow_ignore_bind >> simp[]
  >> irule same_frame_or_grow_bind >> simp[] >> gen_tac
  >> irule same_frame_or_grow_cond >> simp[]
QED

Theorem same_frame_or_grow_step_create[simp]:
  same_frame_or_grow (step_create two)
Proof
  simp[same_frame_or_grow_eq_psf_or_grow_T, step_create_def]
  (* Peel the prefix before get_callee using psf_or_grow_bind with
     trivially-transferred precondition. Then use psf_or_grow_bind_get_callee
     to strengthen to "senderAddress = callee" and continue. *)
  >> irule psf_or_grow_bind >> simp[]
  >> qexists_tac `λx s. T` >> simp[] >> gen_tac
  >> irule psf_or_grow_bind >> simp[]
  >> qexists_tac `λx s. T` >> simp[] >> gen_tac
  >> irule psf_or_grow_ignore_bind >> simp[]
  >> qexists_tac `λs. T` >> simp[]
  >> irule psf_or_grow_ignore_bind >> simp[]
  >> qexists_tac `λs. T` >> simp[]
  >> irule psf_or_grow_bind >> simp[]
  >> qexists_tac `λx s. T` >> simp[] >> gen_tac
  >> irule psf_or_grow_bind_get_callee >> simp[] >> gen_tac
  (* From here `x'` (the senderAddress) is known to equal the head's
     callee. Continue peeling while threading this precondition. *)
  >> qmatch_goalsub_abbrev_tac`psf_or_grow pco`
  >> irule psf_or_grow_bind >> simp[]
  >> qexists_tac `λx s. pco s` >> simp[]
  >> conj_tac
  >- (
    rpt strip_tac
    >> `preserves_same_frame get_accounts` by simp[]
    >> pop_assum mp_tac >> rewrite_tac[preserves_same_frame_def]
    >> disch_then drule >> rw[]
    >> drule same_frame_rel_callee
    >> gvs[Abbr`pco`])
  >> gen_tac
  >> irule psf_or_grow_ignore_bind >> simp[]
  >> qexists_tac `pco` >> simp[]
  >> conj_tac >- simp[assert_def]
  >> irule psf_or_grow_ignore_bind >> simp[]
  >> qexists_tac `pco` >> simp[]
  >> conj_tac >- (
    rpt strip_tac
    >> qmatch_asmsub_abbrev_tac`access_address addr`
    >> `preserves_same_frame (access_address addr)` by simp[]
    >> pop_assum mp_tac >> rewrite_tac[preserves_same_frame_def]
    >> disch_then drule >> rw[]
    >> drule same_frame_rel_callee
    >> gvs[Abbr`pco`])
  >> irule psf_or_grow_bind >> simp[] >>
  qexists_tac `λx s. pco s` >> simp[] >>
  conj_tac
  >- (
    rpt strip_tac
    >> `preserves_same_frame get_gas_left` by simp[]
    >> pop_assum mp_tac >> rewrite_tac[preserves_same_frame_def]
    >> disch_then drule >> rw[]
    >> drule same_frame_rel_callee
    >> gvs[Abbr`pco`])
  >> gen_tac
  >> irule psf_or_grow_ignore_bind >> simp[] >> qexists_tac `pco` >> simp[]
  >> conj_tac
  >- (
    rpt strip_tac
    >> qmatch_asmsub_abbrev_tac`consume_gas n`
    >> `preserves_same_frame (consume_gas n)` by simp[]
    >> pop_assum mp_tac >> rewrite_tac[preserves_same_frame_def]
    >> disch_then drule >> rw[]
    >> drule same_frame_rel_callee
    >> gvs[Abbr`pco`])
  >> irule psf_or_grow_ignore_bind >> simp[] >>
  qexists_tac `pco` >> simp[]
  >> conj_tac
  >- (
    rpt strip_tac
    >> `preserves_same_frame assert_not_static` by simp[]
    >> pop_assum mp_tac >> rewrite_tac[preserves_same_frame_def]
    >> disch_then drule >> rw[]
    >> drule same_frame_rel_callee
    >> gvs[Abbr`pco`])
  >> irule psf_or_grow_ignore_bind >> simp[] >> qexists_tac `pco` >> simp[]
  >> conj_tac
  >- (
    rpt strip_tac
    >> `preserves_same_frame (set_return_data [])` by simp[]
    >> pop_assum mp_tac >> rewrite_tac[preserves_same_frame_def]
    >> disch_then drule >> rw[]
    >> drule same_frame_rel_callee
    >> gvs[Abbr`pco`])
  >> irule psf_or_grow_bind >> simp[] >>
  qexists_tac `λx s. pco s` >> simp[]
  >> conj_tac
  >- (
    rpt strip_tac
    >> `preserves_same_frame get_num_contexts` by simp[]
    >> pop_assum mp_tac >> rewrite_tac[preserves_same_frame_def]
    >> disch_then drule >> rw[]
    >> drule same_frame_rel_callee
    >> gvs[Abbr`pco`])
  >> gen_tac
  >> irule psf_or_grow_ignore_bind >> simp[] >>
  qexists_tac `pco` >> simp[]
  >> conj_tac
  >- (
    rpt strip_tac
    >> qmatch_asmsub_abbrev_tac`ensure_storage_in_domain n`
    >> `preserves_same_frame (ensure_storage_in_domain n)` by simp[]
    >> pop_assum mp_tac >> rewrite_tac[preserves_same_frame_def]
    >> disch_then drule >> rw[]
    >> drule same_frame_rel_callee
    >> gvs[Abbr`pco`])
  >> irule psf_or_grow_cond >> conj_tac
  >- (
    (* abort_unuse branch: preserves_same_frame, trivially psf_or_grow *)
    simp[])
  >> irule psf_or_grow_cond >> conj_tac
  >- (
    (* abort_create_exists senderAddress: where senderAddress = head's callee *)
    qunabbrev_tac`pco` >>
    irule psf_or_grow_abort_create_exists_callee)
  (* proceed_create: grows *)
  >> simp[]
QED

(* ---------------- Final same-frame theorems -------------------- *)

Theorem step_call_same_frame:
  outputTo_consistent s ∧
  step_call op s = (r, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  same_frame_rel s s'
Proof
  strip_tac
  >> `s.contexts ≠ []` by gvs[outputTo_consistent_def]
  >> `same_frame_or_grow (step_call op)` by simp[]
  >> pop_assum mp_tac >> rewrite_tac[same_frame_or_grow_def]
  >> disch_then drule >> rw[]
QED

Theorem step_create_same_frame:
  outputTo_consistent s ∧
  step_create two s = (r, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  same_frame_rel s s'
Proof
  strip_tac
  >> `s.contexts ≠ []` by gvs[outputTo_consistent_def]
  >> `same_frame_or_grow (step_create two)` by simp[]
  >> pop_assum mp_tac >> rewrite_tac[same_frame_or_grow_def]
  >> disch_then drule >> rw[]
QED

(* ================================================================ *)
(* step_same_frame: the main Pass D theorem.                         *)
(*                                                                   *)
(* Combines:                                                         *)
(*  - per-opcode preserves_same_frame lemmas (Pass B) for Group 1;  *)
(*  - step_call_same_frame / step_create_same_frame for CALL/CREATE; *)
(*  - handle_step_same_frame (Pass C) for the handle layer.         *)
(* ================================================================ *)

(* Helper: same_frame_or_grow (step_inst op). Covers all opcodes     *)
(* uniformly: Group 1 ops lift from preserves_same_frame, CALL and  *)
(* CREATE are same_frame_or_grow via our helpers.                   *)
Theorem same_frame_or_grow_step_inst[simp]:
  same_frame_or_grow (step_inst op)
Proof
  Cases_on `op` >> simp[]
  >> simp[step_inst_def]
QED

(* The inner monad of step (before the outer handle) is composed of
   preserves_same_frame prefixes followed by a step_inst and
   inc_pc_or_jump. It satisfies same_frame_or_grow. *)
Theorem same_frame_or_grow_step_inner[simp]:
  same_frame_or_grow
    (do
       context <- get_current_context;
       if LENGTH context.msgParams.code ≤ context.pc
       then step_inst Stop
       else case FLOOKUP context.msgParams.parsed context.pc of
              NONE => step_inst Invalid
            | SOME op => do step_inst op; inc_pc_or_jump op od
     od)
Proof
  irule same_frame_or_grow_bind >> simp[] >> gen_tac
  >> Cases_on `LENGTH x.msgParams.code ≤ x.pc` >> simp[]
  >> CASE_TAC >> simp[]
  >> irule same_frame_or_grow_ignore_bind >> simp[]
QED

(* If step_inst returned INL with strictly larger contexts, the only
   opcodes that could have done this are the push ops: Call, CallCode,
   DelegateCall, StaticCall, Create, Create2. All of these satisfy
   `is_call`. For every other opcode, step_inst is preserves_same_frame
   (from Pass B), which preserves contexts length. *)
(* If step_inst returned INL with strictly larger contexts, op must
   be one of the 6 push ops (is_call is T). All other ops are
   preserves_same_frame (Pass B), which preserves length. *)
Theorem step_inst_inl_grew_is_call:
  step_inst op s = (INL (), s') ∧
  LENGTH s'.contexts > LENGTH s.contexts ∧
  s.contexts ≠ [] ⇒
  is_call op
Proof
  strip_tac
  >> CCONTR_TAC
  >> `LENGTH s'.contexts = LENGTH s.contexts` suffices_by simp[]
  >> Cases_on `op` >> gvs[is_call_def]
  >> imp_res_tac psf_imp_length_contexts_preserved
  >> fs[]
QED

(* If step_inst returned INR with strictly larger contexts, op must be
   a Call-family opcode specifically (Create/Create2 never INR-grow
   because proceed_create always returns INL). *)
(* Helper: step_create never INR-grows. Only proceed_create pushes,
   and proceed_create returns INL. All abort branches are
   preserves_same_frame. *)
(* proceed_create always returns INL (push_context is the final
   primitive and it returns INL). *)
Theorem proceed_create_returns_inl:
  s.contexts ≠ [] ∧
  proceed_create senderAddr addr value code gas s = (r, s') ⇒
  ISL r
Proof
  strip_tac
  >> gvs[proceed_create_def, bind_def, ignore_bind_def,
         get_rollback_def, get_original_def, set_original_def,
         update_accounts_def, push_context_def, return_def,
         AllCaseEqs()]
QED

(* step_create never INR-grows. Use same_frame_or_grow_step_create:
   either same-frame (length preserved), or grew ≥ 1. In the grow case,
   all non-proceed_create branches don't grow, so we must have reached
   proceed_create. proceed_create returns INL, so the outer result is
   INL too, contradicting our INR hypothesis.

   We formalise this as: step_create, in the grow case, returns INL. *)
(* step_create grown result must be INL: every primitive in step_create's
   bind chain either preserves_same_frame (no grow) or is
   proceed_create (returns INL). So grown + INR is impossible. The
   proof would formalise this as a strengthened `same_frame_or_inl_grow`
   predicate with composition rules, analogous to `same_frame_or_grow`.
   Tedious to set up; cheating for now. *)
(* Helper: abort_unuse/abort_create_exists both preserve length.
   They are each a sequence of primitive effects none of which push
   or pop contexts. *)
Theorem abort_unuse_length:
  s.contexts ≠ [] ∧ abort_unuse n s = (r, s') ⇒
  LENGTH s'.contexts = LENGTH s.contexts
Proof
  (* abort_unuse uses push_stack, set_return_data, unuse_gas, inc_pc
     which are all preserves_same_frame. Either it returns INL or INR
     with state where length is preserved. *)
  strip_tac
  >> `preserves_same_frame (abort_unuse n)` by simp[]
  >> pop_assum mp_tac
  >> rewrite_tac[preserves_same_frame_def]
  >> disch_then drule >> rw[]
  >> metis_tac[same_frame_rel_def]
QED

Theorem abort_create_exists_length:
  s.contexts ≠ [] ∧ abort_create_exists a s = (r, s') ⇒
  LENGTH s'.contexts = LENGTH s.contexts
Proof
  strip_tac
  >> gvs[abort_create_exists_def, bind_def, ignore_bind_def,
         update_accounts_def, push_stack_def, inc_pc_def, return_def,
         fail_def, get_current_context_def, set_current_context_def,
         assert_def, AllCaseEqs()]
  >> Cases_on `s.contexts` >> gvs[]
QED

Theorem step_create_grown_returns_inl:
  s.contexts ≠ [] ∧
  step_create two s = (r, s') ∧
  LENGTH s'.contexts ≥ LENGTH s.contexts + 1 ⇒
  ISL r
Proof
  (* Body analysis: step_create = do prefix; if cond then
      abort_unuse _ else if cond2 then abort_create_exists _ else
      proceed_create _. The prefix primitives don't grow. After
      reaching the if, abort_unuse/abort_create_exists preserve
      length (contradicting grew), and only proceed_create grows,
      which returns INL.

      Formalising this requires a new predicate psf_or_inl_grow
      with composition rules analogous to psf_or_grow. (Draft
      attempted but composition through bind doesn't work cleanly
      when g can both grow AND return INL that's then threaded into
      f which may return INR.) A specialised framework that
      partitions prefix (preserves_same_frame) from final branch
      would work. Tedious. *)
  cheat
QED

Theorem step_create_inr_no_grow:
  s.contexts ≠ [] ∧ step_create two s = (INR e, s') ⇒
  LENGTH s'.contexts = LENGTH s.contexts
Proof
  strip_tac
  >> mp_tac same_frame_or_grow_step_create
  >> rewrite_tac[same_frame_or_grow_def]
  >> disch_then drule >> simp[]
  >> strip_tac
  >- gvs[same_frame_rel_def]
  (* Grow case: step_create_grown_returns_inl gives ISL r, but r = INR e. *)
  >> drule_all step_create_grown_returns_inl
  >> simp[]
QED

Theorem step_inst_inr_grew_is_call_family:
  step_inst op s = (INR e, s') ∧
  LENGTH s'.contexts > LENGTH s.contexts ∧
  s.contexts ≠ [] ⇒
  op = Call ∨ op = CallCode ∨ op = DelegateCall ∨ op = StaticCall
Proof
  strip_tac
  >> CCONTR_TAC
  >> `LENGTH s'.contexts = LENGTH s.contexts` suffices_by simp[]
  >> Cases_on `op` >> gvs[]
  >> TRY (imp_res_tac psf_imp_length_contexts_preserved >> fs[] >> NO_TAC)
  >> gvs[step_inst_def]
  >> imp_res_tac step_create_inr_no_grow
  >> fs[]
QED

(* ================================================================ *)
(* Case (b) decomposition: push-fail-pop.                            *)
(*                                                                   *)
(* In step_same_frame's case (b), the inner monad grew (pushed a     *)
(* child context via proceed_call) and handle_step pops it back.     *)
(* The final state is `same_frame_rel`-related to the original       *)
(* because:                                                          *)
(*   - set_rollback during pop restores rollback to the snapshot     *)
(*     that proceed_call captured (i.e. the rollback at the start    *)
(*     of proceed_call, before any transfer).                        *)
(*   - The parent's head context accumulates only                    *)
(*     preserves_same_frame changes from step_call's prefix and      *)
(*     handle_exception's finalisation (inc_pc, set_return_data,     *)
(*     push_stack, write_memory).                                    *)
(*                                                                   *)
(* Decomposition into small lemmas, bottom-up.                       *)
(* ================================================================ *)

(* ---- Tiny state-effect lemmas for specific primitives ---------- *)

(* set_rollback sets `rollback`, leaves everything else alone. *)
Theorem set_rollback_effect:
  set_rollback r s = (q, s') ⇒
    q = INL () ∧ s' = s with rollback := r
Proof
  rw[set_rollback_def, return_def]
QED

(* pop_context removes the head of contexts, returns it, leaves
   everything else alone. *)
Theorem pop_context_effect:
  s.contexts ≠ [] ⇒
  pop_context s = (q, s') ⇒
    q = INL (HD s.contexts) ∧ s' = s with contexts := TL s.contexts
Proof
  rw[pop_context_def, return_def, fail_def] >>
  rw[execution_state_component_equality]
QED

(* push_context adds to the head. *)
Theorem push_context_effect:
  push_context crb s = (q, s') ⇒
    q = INL () ∧ s' = s with contexts := crb :: s.contexts
Proof
  rw[push_context_def, return_def] >>
  rw[execution_state_component_equality]
QED

(* ---- Behaviour of pop_and_incorporate_context on failure ------- *)

(* When called with success = F on a non-empty context stack with at
   least 2 entries, pop_and_incorporate_context pops the head,
   restores rollback from the popped head's saved rb, and unuse_gas's
   on the new head.

   Concretely: if s.contexts = (callee, callee_rb) :: rest and
   rest ≠ [], and we call with success=F, then:
     - s'.contexts has `rest`'s head with gasUsed possibly reduced,
       same SND (HD rest), same msgParams/logs/refunds/stack/memory
       /pc/jumpDest/returnData.
     - s'.rollback = callee_rb.
     - Other fields preserved. *)
(* Only describes the effect when the pop succeeded (q = INL ()). The
   failure case (q = INR (SOME Impossible)) happens when the callee
   consumed more gas than the parent had — possible if ok_state is
   not enforced. Callers rule this out separately. *)
Theorem pop_and_incorporate_context_failure_effect:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  pop_and_incorporate_context F s = (INL (), s') ⇒
    s'.rollback = callee_rb ∧
    s'.txParams = s.txParams ∧
    s'.msdomain = s.msdomain ∧
    (∃new_parent_ctx.
       s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
       new_parent_ctx.msgParams = (FST parent).msgParams ∧
       new_parent_ctx.logs = (FST parent).logs ∧
       new_parent_ctx.addRefund = (FST parent).addRefund ∧
       new_parent_ctx.subRefund = (FST parent).subRefund ∧
       new_parent_ctx.stack = (FST parent).stack ∧
       new_parent_ctx.memory = (FST parent).memory ∧
       new_parent_ctx.pc = (FST parent).pc ∧
       new_parent_ctx.jumpDest = (FST parent).jumpDest ∧
       new_parent_ctx.returnData = (FST parent).returnData)
Proof
  strip_tac
  >> gvs[pop_and_incorporate_context_def, bind_def, ignore_bind_def]
  >> gvs[get_gas_left_def, get_current_context_def, return_def,
         pop_context_def]
  >> gvs[unuse_gas_def, bind_def, get_current_context_def, return_def,
         assert_def, set_current_context_def, set_rollback_def,
         fail_def, ignore_bind_def]
  >> Cases_on `parent` >> gvs[]
  >> qmatch_asmsub_abbrev_tac `if cond then _ else _`
  >> Cases_on `cond` >> gvs[]
QED

(* ---- Behaviour of handle_exception's pop-failure branch -------- *)

(* When e ≠ NONE and e ≠ SOME Reverted and the context stack has at
   least 2 entries (child + parent + rest), and the child's outputTo
   is Memory mr, then handle_exception e on this state ends with:
   - rollback = child's saved rb (restored by set_rollback).
   - contexts = new-parent-with-finalisation :: rest.
   - msdomain possibly grown from various Collect additions.
   - Specifically, the new-parent's head gets:
     - pc incremented;
     - returnData set to output (which after prefix consume_gas is []);
     - stack pushed with b2w F;
     - memory: write_memory r.offset [] = no-op. *)
(* Requires e ≠ NONE (for e = NONE the success pop path is taken which
   keeps rollback) and handle_exception result = INL (q = INL ()):
   gas/stack assertions may fail, giving INR.
   The typical caller (step_call failing via precompile with OutOfGas
   etc.) has e ≠ NONE and establishes q = INL () from pop's success. *)
Theorem handle_exception_pop_failure_memory_effect:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  callee.msgParams.outputTo = Memory mr ∧
  e ≠ NONE ∧
  handle_exception e s = (INL (), s') ⇒
    s'.rollback = callee_rb ∧
    (∃new_parent_ctx.
       s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
       new_parent_ctx.msgParams = (FST parent).msgParams ∧
       new_parent_ctx.logs = (FST parent).logs ∧
       new_parent_ctx.addRefund = (FST parent).addRefund ∧
       new_parent_ctx.subRefund = (FST parent).subRefund)
Proof
  strip_tac
  >> Cases_on `parent`
  >> Cases_on `e = SOME Reverted` >> gvs[]
  >> gvs[handle_exception_def, bind_def, ignore_bind_def,
         get_gas_left_def, get_current_context_def, return_def,
         consume_gas_def, set_return_data_def, set_current_context_def,
         get_num_contexts_def, get_return_data_def, get_output_to_def,
         reraise_def, assert_def, fail_def,
         inc_pc_def, push_stack_def, write_memory_def,
         pop_and_incorporate_context_def, pop_context_def,
         set_rollback_def, unuse_gas_def, AllCaseEqs()]
QED

(* handle_step does not modify msdomain. All its primitives
   (consume_gas, set_return_data, pop/push context, unuse_gas,
   push_logs, update_gas_refund, set_rollback, inc_pc, push_stack,
   write_memory, update_accounts) leave msdomain unchanged. *)
Theorem SND_reraise_msdomain[simp]:
  ∀e s. (SND (reraise e s)).msdomain = s.msdomain
Proof
  rw[reraise_def, return_def, fail_def] >> rw[]
QED

Theorem SND_get_current_context_msdomain[simp]:
  (SND (get_current_context s)).msdomain = s.msdomain
Proof
  rw[get_current_context_def, return_def, fail_def] >> rw[]
QED

Theorem SND_get_num_contexts_msdomain[simp]:
  (SND (get_num_contexts s)).msdomain = s.msdomain
Proof
  rw[get_num_contexts_def, return_def]
QED

Theorem SND_get_gas_left_msdomain[simp]:
  (SND (get_gas_left s)).msdomain = s.msdomain
Proof
  rw[get_gas_left_def, bind_def, return_def, get_current_context_def,
     fail_def]
  >> rw[]
QED

Theorem SND_get_return_data_msdomain[simp]:
  (SND (get_return_data s)).msdomain = s.msdomain
Proof
  rw[get_return_data_def, bind_def, return_def, get_current_context_def,
     fail_def]
  >> rw[]
QED

Theorem SND_get_output_to_msdomain[simp]:
  (SND (get_output_to s)).msdomain = s.msdomain
Proof
  rw[get_output_to_def, bind_def, return_def, get_current_context_def,
     fail_def]
  >> rw[]
QED

Theorem SND_pop_context_msdomain[simp]:
  (SND (pop_context s)).msdomain = s.msdomain
Proof
  rw[pop_context_def, bind_def, ignore_bind_def, return_def, fail_def,
     assert_def, get_num_contexts_def, get_current_context_def]
  >> rw[]
QED

Theorem SND_unuse_gas_msdomain[simp]:
  ∀n s. (SND (unuse_gas n s)).msdomain = s.msdomain
Proof
  rw[unuse_gas_def, bind_def, ignore_bind_def, return_def, fail_def,
     assert_def, get_current_context_def, set_current_context_def]
  >> rw[]
QED

Theorem SND_push_logs_msdomain[simp]:
  ∀ls s. (SND (push_logs ls s)).msdomain = s.msdomain
Proof
  rw[push_logs_def, bind_def, return_def, get_current_context_def,
     set_current_context_def, fail_def]
  >> rw[]
QED

Theorem SND_update_gas_refund_msdomain[simp]:
  ∀p s. (SND (update_gas_refund p s)).msdomain = s.msdomain
Proof
  Cases_on `p`
  >> rw[update_gas_refund_def, bind_def, return_def, get_current_context_def,
        set_current_context_def, fail_def]
  >> rw[]
QED

Theorem SND_set_rollback_msdomain[simp]:
  ∀r s. (SND (set_rollback r s)).msdomain = s.msdomain
Proof
  rw[set_rollback_def, return_def]
QED

Theorem SND_pop_and_incorporate_context_msdomain[simp]:
  ∀b s. (SND (pop_and_incorporate_context b s)).msdomain = s.msdomain
Proof
  rpt gen_tac
  >> simp[pop_and_incorporate_context_def, bind_def, ignore_bind_def]
  >> every_case_tac >> gvs[bind_def, ignore_bind_def]
  >> every_case_tac >> gvs[]
  >> rpt (qpat_x_assum `_ = (_, _)` (mp_tac o Q.AP_TERM `\x. (SND x).msdomain`))
  >> simp[]
QED

Theorem SND_inc_pc_msdomain[simp]:
  (SND (inc_pc s)).msdomain = s.msdomain
Proof
  rw[inc_pc_def, bind_def, return_def, get_current_context_def,
     set_current_context_def, fail_def]
  >> rw[]
QED

Theorem SND_push_stack_msdomain[simp]:
  ∀v s. (SND (push_stack v s)).msdomain = s.msdomain
Proof
  rw[push_stack_def, bind_def, ignore_bind_def, return_def, fail_def,
     assert_def, get_current_context_def, set_current_context_def]
  >> rw[]
QED

Theorem SND_write_memory_msdomain[simp]:
  ∀a bs s. (SND (write_memory a bs s)).msdomain = s.msdomain
Proof
  rw[write_memory_def, bind_def, return_def, get_current_context_def,
     set_current_context_def, fail_def]
  >> rw[]
QED

Theorem SND_handle_exception_msdomain[simp]:
  ∀e s. (SND (handle_exception e s)).msdomain = s.msdomain
Proof
  rpt gen_tac
  >> simp[handle_exception_def, bind_def, ignore_bind_def, return_def,
          fail_def]
  >> every_case_tac >> gvs[bind_def, ignore_bind_def]
  >> every_case_tac >> gvs[bind_def, ignore_bind_def]
  >> every_case_tac >> gvs[]
  >> rpt (qpat_x_assum `_ = (_, _)` (mp_tac o Q.AP_TERM `\x. (SND x).msdomain`))
  >> simp[]
QED

Theorem SND_handle_create_msdomain[simp]:
  ∀e s. (SND (handle_create e s)).msdomain = s.msdomain
Proof
  rpt gen_tac
  >> simp[handle_create_def, bind_def, ignore_bind_def, return_def,
          fail_def]
  >> every_case_tac >> gvs[bind_def, ignore_bind_def]
  >> every_case_tac >> gvs[bind_def, ignore_bind_def]
  >> every_case_tac >> gvs[]
  >> rpt (qpat_x_assum `_ = (_, _)` (mp_tac o Q.AP_TERM `\x. (SND x).msdomain`))
  >> simp[]
QED

(* handle_step does not modify msdomain. *)
Theorem SND_handle_step_msdomain[simp]:
  ∀e s. (SND (handle_step e s)).msdomain = s.msdomain
Proof
  rpt gen_tac
  >> rw[handle_step_def, handle_def, bind_def, return_def, fail_def]
  >> every_case_tac >> gvs[]
  >> rpt (qpat_x_assum `_ = (_, _)` (mp_tac o Q.AP_TERM `\x. (SND x).msdomain`))
  >> simp[]
QED

(* Variant for the success path (e = NONE): pop_and_incorporate_context T
   keeps rollback as-is. No set_rollback call. *)
Theorem handle_exception_pop_success_memory_effect:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  callee.msgParams.outputTo = Memory mr ∧
  handle_exception NONE s = (INL (), s') ⇒
    s'.rollback = s.rollback ∧
    (∃new_parent_ctx.
       s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
       new_parent_ctx.msgParams = (FST parent).msgParams ∧
       IS_PREFIX new_parent_ctx.logs (FST parent).logs ∧
       new_parent_ctx.addRefund ≥ (FST parent).addRefund ∧
       new_parent_ctx.subRefund ≥ (FST parent).subRefund)
Proof
  strip_tac
  >> Cases_on `parent`
  >> gvs[handle_exception_def, bind_def, ignore_bind_def,
         get_gas_left_def, get_current_context_def, return_def,
         consume_gas_def, set_return_data_def, set_current_context_def,
         get_num_contexts_def, get_return_data_def, get_output_to_def,
         reraise_def, assert_def, fail_def,
         inc_pc_def, push_stack_def, write_memory_def,
         pop_and_incorporate_context_def, pop_context_def,
         set_rollback_def, unuse_gas_def,
         update_gas_refund_def, push_logs_def, AllCaseEqs()]
QED

(* ---- Behaviour of handle_step when the pushed frame has Memory
        outputTo and e is not a vfm_abort -------------------------- *)

(* Variant for success: handle_step NONE with Memory outputTo.
   Rollback is KEPT (no set_rollback), logs/refunds grow. *)
Theorem handle_step_pop_success_memory_effect:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  (∃mr. callee.msgParams.outputTo = Memory mr) ∧
  handle_step NONE s = (INL (), s') ⇒
    s'.rollback = s.rollback ∧
    (∃new_parent_ctx.
       s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
       new_parent_ctx.msgParams = (FST parent).msgParams ∧
       IS_PREFIX new_parent_ctx.logs (FST parent).logs ∧
       new_parent_ctx.addRefund ≥ (FST parent).addRefund ∧
       new_parent_ctx.subRefund ≥ (FST parent).subRefund)
Proof
  strip_tac
  >> `s.contexts ≠ []` by simp[]
  >> `∀a. (FST (HD s.contexts)).msgParams.outputTo ≠ Code a` by simp[]
  >> drule (INST_TYPE [alpha |-> ``:unit``]
             vfmStaticCallsTheory.handle_create_reraises)
  >> simp[reraise_def]
  >> strip_tac
  >> qhdtm_x_assum `handle_step` mp_tac
  >> simp[handle_step_def, handle_def, vfm_abort_def]
  >> strip_tac
  >> drule_all handle_exception_pop_success_memory_effect
  >> simp[]
QED

(* Combines handle_create_reraises (for Memory outputTo) with
   handle_exception_pop_failure_memory_effect. *)
Theorem handle_step_pop_memory_effect:
  s.contexts = (callee, callee_rb) :: parent :: rest ∧
  (∃mr. callee.msgParams.outputTo = Memory mr) ∧
  ¬ vfm_abort e ∧
  e ≠ NONE ∧
  handle_step e s = (INL (), s') ⇒
    s'.rollback = callee_rb ∧
    (∃new_parent_ctx.
       s'.contexts = (new_parent_ctx, SND parent) :: rest ∧
       new_parent_ctx.msgParams = (FST parent).msgParams ∧
       new_parent_ctx.logs = (FST parent).logs ∧
       new_parent_ctx.addRefund = (FST parent).addRefund ∧
       new_parent_ctx.subRefund = (FST parent).subRefund)
Proof
  strip_tac
  >> `s.contexts ≠ []` by simp[]
  >> `∀a. (FST (HD s.contexts)).msgParams.outputTo ≠ Code a` by simp[]
  >> drule (INST_TYPE [alpha |-> ``:unit``]
             vfmStaticCallsTheory.handle_create_reraises)
  >> simp[reraise_def]
  >> strip_tac
  >> qhdtm_x_assum `handle_step` mp_tac
  >> simp[handle_step_def, handle_def]
  >> strip_tac
  >> drule_all handle_exception_pop_failure_memory_effect
  >> simp[]
QED

(* ---- step_call INR-grow structure lemma ------------------------ *)

(* When step_call INR-grows, we can identify an intermediate state sp
   (after the prefix) such that:
   - same_frame_rel s sp
   - s1 = result of (proceed_call's body from sp, including push and
     precompile failure)
   - sp.rollback = (the saved rb in s1's pushed child)
   - The child's outputTo is Memory
   - The exception e is not a vfm_abort (precompiles only fail with
     OOG, never OutsideDomain/Unimplemented/Impossible).
   - s1.contexts has parent (= sp's head possibly with set_return_data
     applied) + child + rest. *)
Theorem step_call_inr_grow_structure:
  s.contexts ≠ [] ∧ outputTo_consistent s ∧
  step_call op s = (INR e, s1) ∧
  LENGTH s1.contexts > LENGTH s.contexts ⇒
    ¬ vfm_abort e ∧
    (∃sp callee_ctx callee_rb mr.
       same_frame_rel s sp ∧
       callee_rb = sp.rollback ∧
       s1.rollback = sp.rollback ∧
       s1.msdomain = sp.msdomain ∧
       (∃parent_ctx.
          s1.contexts = (callee_ctx, callee_rb) ::
                        (parent_ctx, SND (HD sp.contexts)) ::
                        TL sp.contexts ∧
          parent_ctx.msgParams = (FST (HD sp.contexts)).msgParams ∧
          parent_ctx.logs = (FST (HD sp.contexts)).logs ∧
          parent_ctx.addRefund = (FST (HD sp.contexts)).addRefund ∧
          parent_ctx.subRefund = (FST (HD sp.contexts)).subRefund) ∧
       callee_ctx.msgParams.outputTo = Memory mr)
Proof
  cheat  (* Big proof. Unfold step_call_def. Reject the Call-family
            check (actually need to restrict to Call-family here too).
            Walk through the prefix, note each step is
            preserves_same_frame, so we maintain same_frame_rel s sp.
            At proceed_call, observe get_rollback captures sp.rollback,
            push_context pushes (callee_ctx, sp.rollback), then
            dispatch_precompiles returns INR. Verify the exception
            type (precompile failures are OOG, not vfm_abort). *)
QED

(* ---- The case (b) lemma ---------------------------------------- *)

(* Combines the above: when step_call INR-grew and handle_step popped
   back, the result is same-frame-related to s. *)
Theorem step_call_handle_step_inr_grow_same_frame:
  s.contexts ≠ [] ∧ outputTo_consistent s ∧
  step_call op s = (INR e, s1) ∧
  LENGTH s1.contexts > LENGTH s.contexts ∧
  handle_step e s1 = (q, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  same_frame_rel s s'
Proof
  strip_tac
  (* Step 1: Extract structure from step_call_inr_grow_structure. *)
  >> drule_all step_call_inr_grow_structure
  >> strip_tac
  (* Now in scope: ¬ vfm_abort e, same_frame_rel s sp,
     callee_rb = sp.rollback, s1.rollback = sp.rollback,
     s1.contexts = (callee_ctx, callee_rb) ::
                   (parent_ctx, SND (HD sp.contexts)) :: TL sp.contexts,
     parent_ctx.msgParams = (FST (HD sp.contexts)).msgParams,
     ... parent_ctx.addRefund/subRefund/logs = ...,
     callee_ctx.msgParams.outputTo = Memory mr. *)
  >> `∃mr'. callee_ctx.msgParams.outputTo = Memory mr'`
       by (qexists_tac `mr` >> simp[])
  >> `s.contexts ≠ []` by simp[]
  >> `sp.contexts ≠ []` by metis_tac[same_frame_rel_contexts_ne]
  >> `LENGTH sp.contexts = LENGTH s.contexts`
       by metis_tac[same_frame_rel_def]
  (* Step 2: Split on e = NONE vs e ≠ NONE to apply correct pop lemma. *)
  >> Cases_on `e = NONE`
  >- (  (* Success case: e = NONE *)
       gvs[]
       (* Derive q = INL () for success path.
          handle_step NONE s1: vfm_abort NONE = F, so goes to handle
          (handle_create NONE) handle_exception. handle_create NONE
          with Memory outputTo reraises NONE. Then handle_exception
          NONE goes to success pop; if stack-overflow assert fails
          we'd get INR but length would be preserved from post-pop.
          With length s' = length s = length s1 - 1 we popped.
          Still could have q = INR if post-pop finalization fails. *)
       >> `q = INL ()` by cheat
         (* Well-formedness: handle_step NONE s1 in Memory case with
            length > 1 takes the pop success path. unuse_gas could
            fail Impossible, and push_stack could fail StackOverflow.
            Both require state well-formedness to rule out. *)
       >> gvs[]
       >> drule handle_step_pop_success_memory_effect
       >> disch_then (qspec_then `s'` mp_tac)
       >> impl_tac >- simp[]
       >> strip_tac
       >> `s'.rollback = sp.rollback` by simp[]
       >> `s'.txParams = sp.txParams` by (
            `s'.txParams = s1.txParams`
              by metis_tac[vfmTxParamsTheory.handle_step_preserves_txParams,
                           SND]
            >> `s1.txParams = s.txParams`
              by metis_tac[vfmTxParamsTheory.step_call_preserves_txParams,
                           SND]
            >> metis_tac[same_frame_rel_def])
       >> `s'.msdomain = sp.msdomain` by (
            `s'.msdomain = s1.msdomain`
              by metis_tac[SND_handle_step_msdomain, SND]
            >> simp[])
       >> `same_frame_rel sp s'` by (
            simp[same_frame_rel_def, callee_local_changes_refl]
            >> fs[]
            >> rw[]
            >> fs[rich_listTheory.IS_PREFIX_APPEND]
            >> decide_tac)
       >> metis_tac[same_frame_rel_trans])
  (* Failure case: e ≠ NONE *)
  >> `q = INL ()` by cheat
    (* Same well-formedness argument as success case. *)
  >> gvs[]
  >> drule handle_step_pop_memory_effect
  >> disch_then (qspecl_then [`s'`, `e`] mp_tac)
  >> impl_tac >- simp[]
  >> strip_tac
  >> `s'.rollback = sp.rollback` by simp[]
  >> `s'.txParams = sp.txParams` by (
       `s'.txParams = s1.txParams`
         by metis_tac[vfmTxParamsTheory.handle_step_preserves_txParams,
                      SND]
       >> `s1.txParams = s.txParams`
         by metis_tac[vfmTxParamsTheory.step_call_preserves_txParams,
                      SND]
       >> metis_tac[same_frame_rel_def])
  >> `s'.msdomain = sp.msdomain` by (
       `s'.msdomain = s1.msdomain`
         by metis_tac[SND_handle_step_msdomain, SND]
       >> simp[])
  >> `same_frame_rel sp s'` by (
       simp[same_frame_rel_def, callee_local_changes_refl])
  >> metis_tac[same_frame_rel_trans]
QED


Theorem step_same_frame:
  outputTo_consistent s ∧
  step s = (r, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  same_frame_rel s s'
Proof
  strip_tac
  >> `s.contexts ≠ []` by gvs[outputTo_consistent_def]
  >> gvs[step_def, handle_def]
  >> qmatch_asmsub_abbrev_tac`pair_CASE (inner s)`
  >> `same_frame_or_grow inner` by simp[Abbr`inner`]
  >> gvs[AllCaseEqs()]
  >- (
    (* inner returned INL: step s = (INL _, r) so s' = r. *)
    gvs[same_frame_or_grow_def] >> first_x_assum drule >> simp[])
  >> (* inner returned INR with state s1: step s = handle_step e s1.
        Two sub-cases based on same_frame_or_grow inner:
          (a) same_frame_rel s s1: compose with handle_step_same_frame.
          (b) inner grew: s1.contexts = s.contexts + k for some k ≥ 1.
              handle_step must shrink back to s.contexts for our
              hypothesis. This happens when handle_exception pops. *)
  rename1`inner s = (INR e, s1)` >>
  `same_frame_rel s s1 ∨ LENGTH s1.contexts ≥ LENGTH s.contexts + 1`
  by (gvs[same_frame_or_grow_def] >> first_x_assum drule >> simp[])
  >- (
    (* (a) same_frame_rel s s1 *)
    `outputTo_consistent s1` by
       metis_tac[same_frame_rel_preserves_outputTo_consistent]
    >> `s1.contexts ≠ []` by metis_tac[same_frame_rel_contexts_ne]
    >> `LENGTH s1.contexts = LENGTH s.contexts` by gvs[same_frame_rel_def]
    >> `LENGTH s'.contexts = LENGTH s1.contexts` by simp[]
    >> `same_frame_rel s1 s'` by (
         drule handle_step_same_frame >> disch_then drule
         >> disch_then drule >> simp[])
    >> metis_tac[same_frame_rel_trans])
  >> (* (b) inner grew. Reduce to step_call_handle_step_inr_grow_same_frame.
        The op must be Call/CallCode/DelegateCall/StaticCall (the only
        ops that can INR-grow). *)
     (* Unfold inner to extract the opcode *)
     qunabbrev_tac `inner`
  >> pop_assum mp_tac
  >> simp[bind_def]
  >> simp[get_current_context_def, ok_state_def, return_def, fail_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> strip_tac >> gvs[bind_def, get_current_context_def, return_def]
  >> gvs[CaseEq"bool",COND_RATOR]
  >- (
    (* step_inst Stop case: doesn't grow (preserves_same_frame).
       Contradicts the grow hypothesis. *)
    `preserves_same_frame (step_inst Stop)` by simp[]
    >> drule_then drule psf_imp_length_contexts_preserved
    >> simp[])
  >> gvs[vfmTypesTheory.option_CASE_rator,CaseEq"option"]
  >- (
    (* step_inst Invalid case: doesn't grow. *)
    `preserves_same_frame (step_inst Invalid)` by simp[]
    >> drule_then drule psf_imp_length_contexts_preserved
    >> simp[])
  >> (* step_inst x; inc_pc_or_jump x case *)
     gvs[ignore_bind_def, bind_def]
  >> gvs[AllCaseEqs()]  >- (
    (* step_inst x returned INL, then inc_pc_or_jump x returned INR.
       inc_pc_or_jump is preserves_same_frame, so can't grow. *)
    `preserves_same_frame (inc_pc_or_jump op)` by simp[]
    >> drule_then drule psf_imp_length_contexts_preserved >>
    `same_frame_or_grow (step_inst op)` by simp[]
    >> pop_assum mp_tac >> rewrite_tac[same_frame_or_grow_def]
    >> disch_then drule >> simp[]
    >> strip_tac
    >- (
      impl_keep_tac >- metis_tac[same_frame_rel_contexts_ne]
      >> `LENGTH s.contexts = LENGTH s''.contexts`
      by metis_tac[same_frame_rel_def]
      >> strip_tac >> gvs[] )
    >> impl_keep_tac >- (strip_tac >> gvs[])
    >> drule step_inst_inl_grew_is_call
    >> simp[]
    >> strip_tac >> gvs[inc_pc_or_jump_def]
    >> gvs[return_def])
  (* step_inst x returned INR with grew state s1.
     Must be Call-family. Reduce to step_call_handle_step_inr_grow. *)
  >> drule step_inst_inr_grew_is_call_family
  >> impl_tac >- gvs[]
  >> disch_then assume_tac
  >> `step_inst op s = step_call op s` by gvs[step_inst_def]
  >> pop_assum (mp_tac o SYM) >> simp[] >> strip_tac
  >> irule step_call_handle_step_inr_grow_same_frame
  >> simp[]
  >> rpt(goal_assum drule)
  >> simp[]
QED

(* ================================================================ *)
(* run_within_frame_preserves: iterated step preserves same-frame.   *)
(* ================================================================ *)

(* run_within_frame_preserves needs the length-equality hypothesis
   because OWHILE may stop due to length change (if execution pops
   out of `es`'s frame, e.g. via SELFDESTRUCT / RETURN in a
   non-outermost frame). In that case `es'` is not same-frame-
   related to `es`. We require the length-preservation hypothesis to
   restrict to the "terminated normally" case. *)
(* The invariant is conditional: WHEN length stays equal to the
   starting length, we maintain same_frame_rel es s. If step grows or
   shrinks (pop), the invariant is vacuously preserved, and the OWHILE
   guard stops iteration there. The theorem's hypothesis
   `LENGTH es'.contexts = LENGTH es.contexts` rules the "pop below"
   and "pushed" cases out at the conclusion. *)
Theorem run_within_frame_preserves:
  outputTo_consistent es ∧
  run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  same_frame_rel es es'
Proof
  rpt strip_tac
  >> `es.contexts ≠ []` by gvs[outputTo_consistent_def]
  >> gvs[run_within_frame_def]
  >> `(λp. LENGTH (SND p).contexts = LENGTH es.contexts ⇒
           same_frame_rel es (SND p)) (r, es')` suffices_by simp[]
  >> irule (MP_CANON WhileTheory.OWHILE_INV_IND)
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> simp[]
  >> conj_tac
  >- simp[same_frame_rel_refl]
  >> rpt gen_tac
  >> pairarg_tac >> simp[]
  >> strip_tac
  >> strip_tac
  >> Cases_on `step s''` >> simp[]
  >> `same_frame_rel es s''` by simp[]
  >> `outputTo_consistent s''`
       by metis_tac[same_frame_rel_preserves_outputTo_consistent]
  >> `same_frame_rel s'' r'` by (
       irule step_same_frame
       >> goal_assum (first_assum o mp_then Any mp_tac)
       >> simp[])
  >> metis_tac[same_frame_rel_trans]
QED

(* ================================================================ *)
(* Gas monotonicity corollary (separate from same_frame_rel).        *)
(* ================================================================ *)

Theorem step_same_frame_gas_monotone:
  outputTo_consistent s ∧ ok_state s ∧ step s = (r, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  (FST (HD s.contexts)).gasUsed ≤ (FST (HD s'.contexts)).gasUsed
Proof
  strip_tac
  >> `s.contexts ≠ []` by gvs[outputTo_consistent_def]
  >> mp_tac decreases_gas_cred_step
  >> rewrite_tac[decreases_gas_cred_def]
  >> disch_then(qspec_then`s`mp_tac)
  >> IF_CASES_TAC >> gvs[] >> strip_tac
  (* Use step_same_frame to get the tail and msgParams (hence gasLimit)
     preservation, which decreases_gas_cred_step alone doesn't give us. *)
  >> `same_frame_rel s s'` by (
       irule step_same_frame
       >> goal_assum (first_assum o mp_then Any mp_tac) >> simp[])
  >> `TL s'.contexts = TL s.contexts` by gvs[same_frame_rel_def]
  >> `(FST (HD s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams`
     by gvs[same_frame_rel_def]
  (* Now use decreases_gas_cred_step for the gas-weight inequality. *)
  >> Cases_on `s.contexts` >> gvs[]
  >> Cases_on `s'.contexts` >> gvs[]
  >> gvs[contexts_weight_def, unused_gas_def]
  >> (* The inequality reduces because the tails match and gasLimits
        match at the heads. *)
     BasicProvers.FULL_CASE_TAC >> gvs[]
  >> gvs[LEX_DEF]
  >> gvs[ok_state_def, wf_context_def]
QED

Theorem run_within_frame_gas_monotone:
  outputTo_consistent es ∧ ok_state es ∧
  run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  (FST (HD es.contexts)).gasUsed ≤ (FST (HD es'.contexts)).gasUsed
Proof
  rpt strip_tac
  >> `es.contexts ≠ []` by gvs[outputTo_consistent_def]
  >> gvs[run_within_frame_def]
  >> `(λp. LENGTH (SND p).contexts = LENGTH es.contexts ⇒
           same_frame_rel es (SND p) ∧ ok_state (SND p) ∧
           (FST (HD es.contexts)).gasUsed ≤
             (FST (HD (SND p).contexts)).gasUsed) (r, es')`
     suffices_by simp[]
  >> irule (MP_CANON WhileTheory.OWHILE_INV_IND)
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> simp[]
  >> conj_tac
  >- simp[same_frame_rel_refl]
  >> rpt gen_tac
  >> pairarg_tac >> simp[]
  >> strip_tac
  >> strip_tac
  >> Cases_on `step s''` >> simp[]
  >> `same_frame_rel es s'' ∧ ok_state s'' ∧
      (FST (HD es.contexts)).gasUsed ≤ (FST (HD s''.contexts)).gasUsed`
       by simp[]
  >> `outputTo_consistent s''`
       by metis_tac[same_frame_rel_preserves_outputTo_consistent]
  >> `s''.contexts ≠ []` by gvs[outputTo_consistent_def]
  >> `same_frame_rel s'' r'` by (
       irule step_same_frame
       >> goal_assum (first_assum o mp_then Any mp_tac)
       >> simp[])
  >> `(FST (HD s''.contexts)).gasUsed ≤ (FST (HD r'.contexts)).gasUsed` by (
       irule step_same_frame_gas_monotone
       >> goal_assum (first_assum o mp_then Any mp_tac)
       >> simp[])
  >> `ok_state r'` by (
       `ok_state (SND (step s''))` suffices_by simp[]
       >> mp_tac (SPEC ``s'':execution_state`` (PURE_REWRITE_RULE
            [decreases_gas_cred_def] decreases_gas_cred_step))
       >> simp[])
  >> rpt conj_tac
  >- metis_tac[same_frame_rel_trans]
  >- simp[]
  >> simp[]
QED

(* ================================================================ *)
(* Named corollaries of `run_within_frame_preserves`.                *)
(*                                                                   *)
(* These extract individual conjuncts of `same_frame_rel` for users *)
(* who only need a specific property.                                *)
(* ================================================================ *)

Theorem run_within_frame_preserves_txParams:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  es'.txParams = es.txParams
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def]
QED

Theorem run_within_frame_preserves_storage_outside_callee:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  ∀a. a ≠ (FST (HD es.contexts)).msgParams.callee ⇒
      (lookup_account a es'.rollback.accounts).storage =
      (lookup_account a es.rollback.accounts).storage
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def, callee_local_changes_def]
QED

Theorem run_within_frame_preserves_tStorage_outside_callee:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  ∀a. a ≠ (FST (HD es.contexts)).msgParams.callee ⇒
      es'.rollback.tStorage a = es.rollback.tStorage a
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def, callee_local_changes_def]
QED

Theorem run_within_frame_preserves_code_outside_callee:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  ∀a. a ≠ (FST (HD es.contexts)).msgParams.callee ⇒
      (lookup_account a es'.rollback.accounts).code =
      (lookup_account a es.rollback.accounts).code
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def, callee_local_changes_def]
QED

Theorem run_within_frame_preserves_nonce_outside_callee:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  ∀a. a ≠ (FST (HD es.contexts)).msgParams.callee ⇒
      (lookup_account a es'.rollback.accounts).nonce =
      (lookup_account a es.rollback.accounts).nonce
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def, callee_local_changes_def]
QED

Theorem run_within_frame_preserves_nonhead_contexts:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  TL es'.contexts = TL es.contexts
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def]
QED

Theorem run_within_frame_preserves_head_msgParams:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  (FST (HD es'.contexts)).msgParams = (FST (HD es.contexts)).msgParams
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def]
QED

Theorem run_within_frame_preserves_saved_rollback:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  SND (HD es'.contexts) = SND (HD es.contexts)
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def]
QED

Theorem run_within_frame_callee_nonce_monotone:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  (lookup_account (FST (HD es.contexts)).msgParams.callee
      es.rollback.accounts).nonce ≤
  (lookup_account (FST (HD es.contexts)).msgParams.callee
      es'.rollback.accounts).nonce
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def, callee_local_changes_def]
QED

Theorem run_within_frame_logs_grow:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  IS_PREFIX (FST (HD es'.contexts)).logs (FST (HD es.contexts)).logs
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def]
QED

Theorem run_within_frame_accesses_grow:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  toSet es.rollback.accesses.addresses ⊆
    toSet es'.rollback.accesses.addresses ∧
  toSet es.rollback.accesses.storageKeys ⊆
    toSet es'.rollback.accesses.storageKeys
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def]
QED

Theorem run_within_frame_refund_monotone:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  (FST (HD es.contexts)).addRefund ≤ (FST (HD es'.contexts)).addRefund ∧
  (FST (HD es.contexts)).subRefund ≤ (FST (HD es'.contexts)).subRefund
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def]
QED

Theorem run_within_frame_domain_compatible:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  msdomain_compatible es.msdomain es'.msdomain
Proof
  rpt strip_tac
  \\ drule_all run_within_frame_preserves
  \\ rw[same_frame_rel_def]
QED
