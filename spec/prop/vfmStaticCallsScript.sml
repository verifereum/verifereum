Theory vfmStaticCalls
Ancestors
  pair
  vfmExecution vfmDecreasesGas vfmExecutionProp vfmPreserves

(*
  Proof that static calls do not modify world state.

  Architecture:
  1. static_inv: invariant over full execution state
  2. cp: context-preserving monadic property
  3. Decompose step = handle inner handle_step
  4. Prove inner preserves via cp + special cases
  5. Prove handle_step preserves
  6. run_tr induction lifts to run
  7. Final theorem connects to the frozen statement
*)

Definition static_inv_def:
  static_inv a0 t0 d0 l0 s ⇔
    s.rollback.accounts = a0 ∧
    s.rollback.tStorage = t0 ∧
    s.rollback.toDelete = d0 ∧
    s.contexts ≠ [] ∧
    EVERY (λ(ctxt, rb). ctxt.msgParams.static ∧
      (∀a. ctxt.msgParams.outputTo ≠ Code a)) s.contexts ∧
    EVERY (λ(ctxt, rb).
      ctxt.logs = [] ∧
      rb.accounts = a0 ∧ rb.tStorage = t0 ∧ rb.toDelete = d0)
      (FRONT s.contexts) ∧
    (FST (LAST s.contexts)).logs = l0
End

Theorem handle_snd_split:
  (∀r' s'. f s = (r', s') ⇒ P s') ∧
  (∀e s' r'' s''. f s = (INR e, s') ∧ h e s' = (r'', s'') ⇒ P s'')
  ⇒ P (SND (handle f h s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_isl_split:
  (∀x s'. f s = (INL x, s') ⇒ P) ∧
  (∀e s'. f s = (INR e, s') ⇒ ISL (FST (h e s')) ⇒ P)
  ⇒ ISL (FST (handle f h s)) ⇒ P
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem assert_not_static_static:
  q.msgParams.static ∧ s.contexts = (q,r)::t ⇒
  assert_not_static s = (INR (SOME WriteInStaticContext), s)
Proof
  cheat  (* SCAFFOLD *)
QED

(* ---- cp: context-preserving monadic property ---- *)

Definition cp_def:
  cp (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ∧ s.contexts ≠ [] ⇒
      s'.originalAccounts = s.originalAccounts ∧
      s'.rollback.accounts = s.rollback.accounts ∧
      s'.rollback.tStorage = s.rollback.tStorage ∧
      s'.rollback.toDelete = s.rollback.toDelete ∧
      ∃q'. s'.contexts = (q', SND (HD s.contexts)) :: TL s.contexts ∧
           q'.msgParams = (FST (HD s.contexts)).msgParams ∧
           q'.logs = (FST (HD s.contexts)).logs
End

(* ================================================================== *)
(* cp_rel: the state relation underlying cp.                           *)
(*                                                                    *)
(* cp_rel captures exactly what cp says: rollback.accounts, tStorage,  *)
(* and toDelete are preserved, the head context agrees on msgParams  *)
(* and logs, and the tail is unchanged. NOTE: cp_rel does NOT        *)
(* preserve rollback.accesses — operations like access_address and  *)
(* access_slot modify accesses while being cp.                         *)
(* ================================================================== *)

Definition cp_rel_def:
  cp_rel s s' ⇔
    s'.originalAccounts = s.originalAccounts ∧
    s'.rollback.accounts = s.rollback.accounts ∧
    s'.rollback.tStorage = s.rollback.tStorage ∧
    s'.rollback.toDelete = s.rollback.toDelete ∧
    (s.contexts ≠ [] ⇒
      ∃q'. s'.contexts = (q', SND (HD s.contexts)) :: TL s.contexts ∧
           q'.msgParams = (FST (HD s.contexts)).msgParams ∧
           q'.logs = (FST (HD s.contexts)).logs)
End

Theorem cp_eq_preserves_when:
  cp m ⇔ preserves_when (λs. s.contexts ≠ []) cp_rel m
Proof
  cheat  (* SCAFFOLD *)
QED

(* ================================================================== *)
(* Reflexivity and transitivity of cp_rel.                             *)
(* Needed for the generic preserves_when composition lemmas.          *)
(* ================================================================== *)

Theorem cp_rel_refl:
  s.contexts ≠ [] ⇒ cp_rel s s
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_rel_trans:
  cp_rel s1 s2 ∧ cp_rel s2 s3 ⇒ cp_rel s1 s3
Proof
  cheat  (* SCAFFOLD *)
QED

(* cp_rel preserves non-empty contexts (precondition transfer).       *)
Theorem cp_rel_contexts_ne:
  s.contexts ≠ [] ∧ cp_rel s s' ⇒ s'.contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

(* Composition lemmas (derived from the generic preserves_when     *)
(* framework via cp_eq_preserves_when + cp_rel_trans / cp_rel_refl / *)
(* cp_rel_contexts_ne).                                            *)
Theorem cp_bind[simp]:
  cp g ∧ (∀x. cp (f x)) ⇒ cp (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_ignore_bind[simp]:
  cp g ∧ cp f ⇒ cp (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_handle[simp]:
  cp f ∧ (∀e. cp (h e)) ⇒ cp (handle f h)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_cond[simp]:
  cp m1 ∧ cp m2 ⇒ cp (if b then m1 else m2)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_case_option[simp]:
  cp m_none ∧ (∀x. cp (m_some x)) ⇒
  cp (case opt of NONE => m_none | SOME x => m_some x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_case_sum[simp]:
  (∀x. cp (f x)) ∧ (∀y. cp (g y)) ⇒
  cp (case s of INL x => f x | INR y => g y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_case_pair[simp]:
  (∀x y. cp (f x y)) ⇒ cp (case p of (x, y) => f x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_let[simp]:
  (∀x. cp (f x)) ⇒ cp (let x = v in f x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_preserves_static_inv:
  cp m ∧ static_inv a0 t0 d0 l0 s ⇒
  static_inv a0 t0 d0 l0 (SND (m s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* Paired version: when m s = (r, s'), static_inv transfers to s' *)
Theorem cp_preserves_static_inv_pair:
  cp m /\ static_inv a0 t0 d0 l0 s /\ m s = (r, s') ==>
  static_inv a0 t0 d0 l0 s'
Proof
  cheat  (* SCAFFOLD *)
QED

(* General tactic for proving cp of leaf operations *)
val basic_defs = [bind_def, return_def, fail_def, assert_def,
  ignore_bind_def, reraise_def,
  get_current_context_def, set_current_context_def];

val cp_tac = fn defs =>
  rw[cp_def] >> rpt strip_tac
  >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h` >> gvs[]
  >> gvs (AllCaseEqs()::defs @ basic_defs);

(* Leaf cp facts *)
Theorem cp_leaves[simp]:
  cp (return x) ∧ cp (fail e) ∧ cp (reraise (eo : exception option)) ∧ cp (assert b e) ∧
  cp (consume_gas n) ∧ cp (push_stack w) ∧ cp (pop_stack n) ∧
  cp (set_return_data rd) ∧ cp inc_pc ∧ cp finish ∧ cp revert ∧
  cp assert_not_static ∧
  cp (access_address a) ∧ cp (access_slot sk) ∧
  cp (set_jump_dest d) ∧ cp (update_gas_refund (a0, s0)) ∧
  cp (ensure_storage_in_domain a')
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_update_gas_refund[simp]:
  cp (update_gas_refund updates)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Getters are cp (they just read state) *)
Theorem cp_getters[simp]:
  cp get_tx_params ∧ cp get_accounts ∧ cp get_rollback ∧
  cp get_current_code ∧ cp get_call_data ∧
  cp get_current_context ∧ cp get_callee ∧ cp get_caller ∧
  cp get_value ∧ cp get_num_contexts ∧ cp get_gas_left ∧
  cp get_static ∧ cp get_output_to ∧ cp get_return_data ∧
  cp get_tStorage
Proof
  cheat  (* SCAFFOLD *)
QED

(* Memory operations are cp *)
Theorem cp_memory[simp]:
  cp (write_memory off ws) ∧ cp (read_memory off sz) ∧
  cp (expand_memory n) ∧ cp (memory_expansion_info off sz)
Proof
  cheat  (* SCAFFOLD *)
QED

(* get_context >> set_current_context preserving msgParams/logs is cp *)
Theorem cp_get_set_context:
  (∀ctxt. (f ctxt).msgParams = ctxt.msgParams) ∧
  (∀ctxt. (f ctxt).logs = ctxt.logs) ⇒
  cp (bind get_current_context (λctxt. set_current_context (f ctxt)))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_get_cp_set_context:
  (∀ctxt. cp (g ctxt)) ∧
  (∀ctxt x. (f ctxt x).msgParams = ctxt.msgParams) ∧
  (∀ctxt x. (f ctxt x).logs = ctxt.logs) ⇒
  cp (bind get_current_context (λctxt. bind (g ctxt) (λx. set_current_context (f ctxt x))))
Proof
  cheat  (* SCAFFOLD *)
QED

(* Tactic for compound cp proofs: unfold def then repeatedly apply composition *)
val cp_simp_tac = fn defs =>
  rw defs
  >> rpt (irule cp_bind >> rw[]
          ORELSE irule cp_ignore_bind >> rw[]
          ORELSE irule cp_handle >> rw[]
          ORELSE irule cp_get_set_context >> rw[]);

(* inc_pc_or_jump is cp *)
Theorem cp_inc_pc_or_jump[simp]:
  cp (inc_pc_or_jump op)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_unuse_gas[simp]:
  cp (unuse_gas n)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Composition: cp prefix + static_inv-preserving continuation *)
Theorem static_inv_bind_cp:
  cp g /\ (!x s. static_inv a0 t0 d0 l0 s /\ s.contexts <> [] ==>
                  static_inv a0 t0 d0 l0 (SND (f x s))) /\
  static_inv a0 t0 d0 l0 s ==>
  static_inv a0 t0 d0 l0 (SND (bind g f s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* Variant for ignore_bind *)
Theorem static_inv_ignore_bind_cp:
  cp g /\ (!s. static_inv a0 t0 d0 l0 s /\ s.contexts <> [] ==>
               static_inv a0 t0 d0 l0 (SND (f s))) /\
  static_inv a0 t0 d0 l0 s ==>
  static_inv a0 t0 d0 l0 (SND (ignore_bind g f s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* LET variant *)
Theorem static_inv_let:
  (!x. static_inv a0 t0 d0 l0 (SND (f x s))) ==>
  static_inv a0 t0 d0 l0 (SND ((let x = v in f x) s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* Cond variant *)
Theorem static_inv_cond:
  static_inv a0 t0 d0 l0 (SND (f1 s)) /\
  static_inv a0 t0 d0 l0 (SND (f2 s)) ==>
  static_inv a0 t0 d0 l0 (SND ((if b then f1 else f2) s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* Under static_inv, bind assert_not_static f preserves inv (fails before f runs) *)
Theorem static_inv_assert_not_static:
  static_inv a0 t0 d0 l0 s ==>
  static_inv a0 t0 d0 l0 (SND (bind assert_not_static f s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* ignore_bind variant *)
Theorem static_inv_ignore_bind_assert:
  static_inv a0 t0 d0 l0 s ==>
  static_inv a0 t0 d0 l0 (SND (ignore_bind assert_not_static f s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* When cp g and static_inv, bind g (.. assert_not_static ..) preserves inv *)
Theorem cp_then_static_fail:
  cp g ∧ static_inv a0 t0 d0 l0 s ⇒
  ¬ISL (FST (bind g (λx. bind assert_not_static (f x)) s)) ∧
  static_inv a0 t0 d0 l0 (SND (bind g (λx. bind assert_not_static (f x)) s))
Proof
  cheat  (* SCAFFOLD *)
QED


Theorem cp_precompiles[simp]:
  cp precompile_ecrecover ∧
  cp precompile_sha2_256 ∧
  cp precompile_ripemd_160 ∧
  cp precompile_identity ∧
  cp precompile_modexp ∧
  cp precompile_ecadd ∧
  cp precompile_ecmul ∧
  cp precompile_ecpairing ∧
  cp precompile_blake2f ∧
  cp precompile_point_eval ∧
  cp precompile_bls_g1add ∧
  cp precompile_bls_g1msm ∧
  cp precompile_bls_g2add ∧
  cp precompile_bls_g2msm ∧
  cp precompile_bls_pairing ∧
  cp precompile_bls_map_fp_to_g1 ∧
  cp precompile_bls_map_fp2_to_g2 ∧
  cp precompile_p256verify
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_dispatch_precompiles[simp]:
  cp (dispatch_precompiles addr)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_copy_to_memory[simp]:
  (∀f. src = SOME f ⇒ cp f) ⇒
  cp (copy_to_memory gas off srcOff sz src)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_get_code[simp]:
  cp (get_code addr)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_get_return_data_check[simp]:
  cp (get_return_data_check off sz)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_get_original[simp]:
  cp get_original
Proof
  cheat  (* SCAFFOLD *)
QED


(* EIP-8037: the state gas meter reads and writes the head frame's gas
   fields, which `cp` does not constrain beyond `msgParams` and `logs`. *)
Theorem cp_state_gas_meter[simp]:
  cp get_state_gas_left ∧ cp (charge_state_gas n) ∧
  cp (credit_state_gas_refund n) ∧ cp restore_state_gas ∧
  cp commit_state_gas ∧ cp (restore_state_gas_to_entry sg) ∧
  cp repay_state_gas_spill ∧ cp forfeit_remaining_gas ∧
  cp withhold_create_gas ∧ cp drain_state_gas_reservoir ∧
  cp (restore_child_gas g sr)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_step_sstore_gas[simp]:
  cp (step_sstore_gas_consumption addr key value)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_step_helpers[simp]:
  cp step_mload ∧ cp step_keccak256 ∧
  cp step_ext_code_copy ∧ cp step_return_data_copy ∧
  (∀t. cp (step_sload t)) ∧
  (∀b. cp (step_return b))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_step_copy_to_memory[simp]:
  (∀f. src = SOME f ⇒ cp f) ⇒
  cp (step_copy_to_memory op src)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_step_swap[simp]:
  ∀n. cp (step_swap n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_step_swapn[simp]:
  cp step_swapn
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_step_exchange[simp]:
  cp step_exchange
Proof
  cheat  (* SCAFFOLD *)
QED

(* All non-guarded, non-call step_inst ops are cp *)
Theorem cp_step_inst_non_call[simp]:
  op ≠ SStore ∧ op ≠ TStore ∧ (∀n. op ≠ Log n) ∧
  op ≠ SelfDestruct ∧ op ≠ Create ∧ op ≠ Create2 ∧
  op ≠ Call ∧ op ≠ CallCode ∧ op ≠ DelegateCall ∧ op ≠ StaticCall
  ⇒ cp (step_inst op)
Proof
  cheat  (* SCAFFOLD *)
QED

(* When f returns INR, projections of handle f h s equal projections of h e s' *)
Theorem handle_INR_eq:
  f s = (INR e, s') ==> handle f h s = h e s'
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_INR_snd:
  f s = (INR e, s') ==> SND (handle f h s) = SND (h e s')
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_INR_fst:
  f s = (INR e, s') ==> FST (handle f h s) = FST (h e s')
Proof
  cheat  (* SCAFFOLD *)
QED

(* When outputTo ≠ Code for current context, handle_create just reraises *)
Theorem handle_create_reraises:
  (∀a. (FST (HD s.contexts)).msgParams.outputTo ≠ Code a) ∧
  s.contexts ≠ [] ⇒
  handle_create e s = reraise e s
Proof
  cheat  (* SCAFFOLD *)
QED

(* push_logs [] is cp — callee had no logs under invariant *)
Theorem cp_push_logs_nil:
  cp (push_logs [])
Proof
  cheat  (* SCAFFOLD *)
QED

(* after_pop is cp *)
Theorem cp_after_pop[simp]:
  cp (after_pop a b c)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Abbreviation for the 5 conclusions we need *)
(* static_conclusions val removed — simplified theorems conclude with
   static_inv directly instead of 5 separate conjuncts *)

(* The cp prefix of handle_exception *)
Theorem cp_handle_exception_prefix:
  cp (if ~success /\ e <> SOME Reverted then
        ignore_bind (bind get_gas_left
          (\gasLeft. ignore_bind (consume_gas gasLeft)
            (set_return_data []))) (return ())
      else return ())
Proof
  cheat  (* SCAFFOLD *)
QED

(* Decompose handle_exception into cp prefix + handle_ex_helper *)
Theorem handle_exception_decomp:
  handle_exception e s =
  (let prefix = (if ~(e = NONE) /\ e <> SOME Reverted then
     do gasLeft <- get_gas_left; consume_gas gasLeft; set_return_data [] od
   else return ()) in
   bind prefix (\u. handle_ex_helper e) s)
Proof
  cheat  (* SCAFFOLD *)
QED

(* pop_and_incorporate_context preserves static_inv.
   Key: callee (head) has logs=[] from FRONT, so push_logs [] = no-op.
   Caller's logs are preserved. LAST is unchanged or becomes head. *)
Theorem pop_incorporate_static:
  static_inv a0 t0 d0 l0 s /\ 1 < LENGTH s.contexts ==>
  static_inv a0 t0 d0 l0
    (SND (pop_and_incorporate_context success s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* handle_ex_helper preserves static_inv *)
Theorem handle_ex_helper_static_inv:
  static_inv a0 t0 d0 l0 s ==>
  static_inv a0 t0 d0 l0 (SND (handle_ex_helper e s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* handle_exception preserves static_inv *)
Theorem handle_exception_static_inv:
  static_inv a0 t0 d0 l0 s ==>
  static_inv a0 t0 d0 l0 (SND (handle_exception e s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* handle_step preserves static_inv *)
Theorem handle_step_static_inv:
  static_inv a0 t0 d0 l0 s ==>
  static_inv a0 t0 d0 l0 (SND (handle_step e s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* Lifting lemma: if inner preserves static_inv, then handle inner handle_step
   also preserves static_inv *)
Theorem handle_step_lift:
  (!r s'. inner s0 = (r, s') ==> static_inv a0 t0 d0 l0 s') ==>
  static_inv a0 t0 d0 l0 s0 ==>
  static_inv a0 t0 d0 l0
    (SND (handle (inner:unit execution) handle_step s0))
Proof
  cheat  (* SCAFFOLD *)
QED

(* LET with UNCURRY (for tuple let-bindings like (a,b) <<- expr) *)
Theorem static_inv_let_uncurry:
  (!a b. static_inv a0 t0 d0 l0 (SND (f a b s))) ==>
  static_inv a0 t0 d0 l0 (SND (LET (UNCURRY (\a b. f a b)) v s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* Direct UNCURRY application (after LET reduction) *)
Theorem static_inv_uncurry:
  (!a b. static_inv a0 t0 d0 l0 (SND (f a b s))) ==>
  static_inv a0 t0 d0 l0 (SND (UNCURRY f p s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* ignore_bind where first op is conditional assert_not_static.
   When b=T, assert_not_static fails under static_inv (state unchanged).
   When b=F, return () is a no-op and we continue with ~b available. *)
Theorem static_inv_ignore_bind_assert_cond:
  static_inv a0 t0 d0 l0 s /\
  (~b ==> static_inv a0 t0 d0 l0 (SND (f s))) ==>
  static_inv a0 t0 d0 l0
    (SND (ignore_bind (if b then assert_not_static else return ()) f s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* Tactic: step through a monadic chain under static_inv.
   Repeatedly decomposes bind/ignore_bind/let/cond into cp prefix + rest,
   stopping when it hits assert_not_static (which kills the chain). *)
(* Solve trivial subgoals from irule: cp facts + assumptions *)
val solve_side = simp[] ORELSE first_assum ACCEPT_TAC;
val static_inv_step =
  rpt (CHANGED_TAC (
    irule static_inv_assert_not_static
    ORELSE irule static_inv_ignore_bind_assert
    ORELSE (irule static_inv_ignore_bind_assert_cond >> conj_tac
            >- first_assum ACCEPT_TAC >> strip_tac)
    ORELSE (irule static_inv_uncurry >> rpt strip_tac)
    ORELSE (irule static_inv_bind_cp >> TRY solve_side
            >> TRY (simp[pairTheory.FORALL_PROD] >> rpt strip_tac))
    ORELSE (irule static_inv_ignore_bind_cp >> TRY solve_side
            >> TRY (rpt strip_tac))
    ORELSE (irule static_inv_let_uncurry >> TRY (rpt strip_tac))
    ORELSE (irule static_inv_let >> TRY (rpt strip_tac))
    ORELSE (irule static_inv_cond)
    ORELSE solve_side));

(* Guarded ops all have: cp_prefix >> assert_not_static >> rest *)
Theorem guarded_op_preserves_static_inv:
  static_inv a0 t0 d0 l0 s /\ s.contexts <> [] ==>
  static_inv a0 t0 d0 l0 (SND (step_sstore transient s)) /\
  static_inv a0 t0 d0 l0 (SND (step_log n s)) /\
  static_inv a0 t0 d0 l0 (SND (step_self_destruct s)) /\
  static_inv a0 t0 d0 l0 (SND (step_create two s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* proceed_call preserves static_inv when:
   - value = 0 or op = CallCode (so update_accounts is skipped)
   - subStatic = T (so new context is static)
   - outputTo = Memory mr (so outputTo <> Code) *)
Theorem static_inv_push_context:
  static_inv a0 t0 d0 l0 s /\ s.contexts <> [] /\
  ctxt.msgParams.static /\ ctxt.logs = [] /\
  (!a. ctxt.msgParams.outputTo <> Code a) /\
  rb.accounts = a0 /\ rb.tStorage = t0 /\ rb.toDelete = d0 ==>
  static_inv a0 t0 d0 l0 (SND (push_context (ctxt, rb) s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* Composition: push_context followed by cp suffix *)
Theorem static_inv_ignore_bind_push_context:
  cp f /\
  ctxt.msgParams.static /\ ctxt.logs = [] /\
  (!a. ctxt.msgParams.outputTo <> Code a) /\
  rb.accounts = a0 /\ rb.tStorage = t0 /\ rb.toDelete = d0 /\
  static_inv a0 t0 d0 l0 s /\ s.contexts <> [] ==>
  static_inv a0 t0 d0 l0 (SND (ignore_bind (push_context (ctxt, rb)) f s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_call_preserves_static_inv:
  static_inv a0 t0 d0 l0 s /\ s.contexts <> [] /\
  (value = 0 \/ op = CallCode) ==>
  static_inv a0 t0 d0 l0
    (SND (proceed_call op sender address value
       argsOff argsSize code stipend (Memory mr) s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_abort_call_value[simp]:
  cp (abort_call_value n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_abort_unuse[simp]:
  cp (abort_unuse n)
Proof
  cheat  (* SCAFFOLD *)
QED

(*
  step_call proof strategy:
  - For op=Call: assert_not_static always fails under static_inv,
    so the entire continuation after it is dead code. The cp prefix
    before assert_not_static preserves static_inv.
  - For op<>Call: the guard simplifies to return() (no-op),
    and proceed_call has value=0 or op=CallCode.
*)
Theorem step_call_Call_static:
  static_inv a0 t0 d0 l0 s /\ s.contexts <> [] ==>
  static_inv a0 t0 d0 l0 (SND (step_call Call s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_nonCall_static:
  op <> Call ==>
  static_inv a0 t0 d0 l0 s /\ s.contexts <> [] ==>
  static_inv a0 t0 d0 l0 (SND (step_call op s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_preserves_static_inv:
  static_inv a0 t0 d0 l0 s /\ s.contexts <> [] ==>
  static_inv a0 t0 d0 l0 (SND (step_call op s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inst_preserves_static_inv:
  static_inv a0 t0 d0 l0 s /\ s.contexts <> [] ==>
  static_inv a0 t0 d0 l0 (SND (step_inst op s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inner_preserves_static_inv:
  static_inv a0 t0 d0 l0 s /\ s.contexts <> [] ==>
  !r s'. (do
    ctxt <- get_current_context;
    case FLOOKUP ctxt.msgParams.parsed ctxt.pc of
    | SOME op => do step_inst op; inc_pc_or_jump op od
    | NONE =>
        if LENGTH ctxt.msgParams.code <= ctxt.pc then step_inst Stop
        else step_inst Invalid
  od) s = (r, s') ==>
  static_inv a0 t0 d0 l0 s'
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_preserves_static_inv:
  static_inv a0 t0 d0 l0 s0 ==>
  static_inv a0 t0 d0 l0 (SND (step s0))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_tr_preserves_static_inv:
  ∀r s. static_inv a0 t0 d0 l0 s ⇒
  static_inv a0 t0 d0 l0 (SND (run_tr (r, s)))
Proof
  cheat  (* SCAFFOLD *)
QED

(* TODO: the outputTo ≠ Code precondition should be removable by moving
   outputTo ≠ Code from ALL to FRONT in static_inv (vacuous for singleton) *)
Theorem run_static_preserves:
  ∀es result final_state ctxt rb.
    run es = SOME (INR result, final_state) ∧
    es.contexts = [(ctxt, rb)] ∧
    ctxt.msgParams.static ∧
    (∀a. ctxt.msgParams.outputTo ≠ Code a) ⇒
    final_state.rollback.accounts = es.rollback.accounts ∧
    final_state.rollback.tStorage = es.rollback.tStorage ∧
    final_state.rollback.toDelete = es.rollback.toDelete ∧
    (case final_state.contexts of
       [(ctxt', _)] => ctxt'.logs = ctxt.logs
     | _ => T)
Proof
  cheat  (* SCAFFOLD *)
QED

(* ---------- static_not_code (snc) invariant ---------- *)

(* snc: every static context has outputTo ≠ Code *)
Definition snc_def:
  snc s ⇔ EVERY (λ(c,r). c.msgParams.static ⇒
    ∀a. c.msgParams.outputTo ≠ Code a) s.contexts
End

(* cp preserves snc *)
Theorem cp_preserves_snc:
  cp m ∧ snc s ∧ s.contexts ≠ [] ⇒ snc (SND (m s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_preserves_snc_pair:
  cp m ∧ snc s ∧ s.contexts ≠ [] ∧ m s = (r, s') ⇒ snc s'
Proof
  cheat  (* SCAFFOLD *)
QED

(* pop_and_incorporate_context preserves snc:
   pops head context, then does cp operations on new head *)
Theorem pop_incorporate_snc:
  snc s ∧ s.contexts ≠ [] ∧ 1 < LENGTH s.contexts ⇒
  snc (SND (pop_and_incorporate_context success s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* General: cp preserves contexts ≠ [] *)
Theorem cp_contexts_ne:
  cp m ∧ s.contexts ≠ [] ⇒ (SND (m s)).contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_contexts_ne_pair:
  cp m ∧ s.contexts ≠ [] ∧ m s = (r, s') ⇒ s'.contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

(* context-preserving: a weaker property than cp —
   only requires contexts structure preservation (not rollback) *)
Definition ctx_pres_def:
  ctx_pres (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ∧ s.contexts ≠ [] ⇒
      ∃q'. s'.contexts = (q', SND (HD s.contexts)) :: TL s.contexts ∧
           q'.msgParams = (FST (HD s.contexts)).msgParams
End

Theorem cp_is_ctx_pres:
  cp m ⇒ ctx_pres m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ctx_pres_preserves_snc:
  ctx_pres m ∧ snc s ∧ s.contexts ≠ [] ⇒ snc (SND (m s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ctx_pres_bind[simp]:
  ctx_pres g ∧ (∀x. ctx_pres (f x)) ⇒ ctx_pres (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ctx_pres_ignore_bind[simp]:
  ctx_pres g ∧ ctx_pres f ⇒ ctx_pres (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ctx_pres_update_accounts[simp]:
  ctx_pres (update_accounts f)
Proof
  cheat  (* SCAFFOLD *)
QED

(* ctx_pres composition lemmas *)
Theorem ctx_pres_leaves[simp]:
  ctx_pres (return x) ∧ ctx_pres (fail e) ∧
  ctx_pres (reraise eo) ∧ ctx_pres (assert b e) ∧
  ctx_pres (consume_gas n) ∧ ctx_pres (update_accounts f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ctx_pres_cond[simp]:
  ctx_pres m1 ∧ ctx_pres m2 ⇒ ctx_pres (if b then m1 else m2)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ctx_pres_case_option[simp]:
  ctx_pres m_none ∧ (∀x. ctx_pres (m_some x)) ⇒
  ctx_pres (case opt of NONE => m_none | SOME x => m_some x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ctx_pres_case_sum[simp]:
  (∀x. ctx_pres (f x)) ∧ (∀y. ctx_pres (g y)) ⇒
  ctx_pres (case s of INL x => f x | INR y => g y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ctx_pres_case_pair[simp]:
  (∀x y. ctx_pres (f x y)) ⇒ ctx_pres (case p of (x, y) => f x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ctx_pres_let[simp]:
  (∀x. ctx_pres (f x)) ⇒ ctx_pres (let x = v in f x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ctx_pres_handle[simp]:
  ctx_pres f ∧ (∀e. ctx_pres (h e)) ⇒ ctx_pres (handle f h)
Proof
  cheat  (* SCAFFOLD *)
QED

(* handle_create preserves snc: it either reraises (no state change)
   or does consume_gas (cp) + update_accounts (contexts unchanged) + reraise *)
Theorem handle_create_snc:
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (handle_create e s)) ∧
  (SND (handle_create e s)).contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

(* Pair-aware version: avoids polymorphic type mismatch on SND *)
Theorem handle_create_snc_pair[local]:
  handle_create e s = (r, s') ∧ snc s ∧ s.contexts ≠ [] ⇒
  snc s' ∧ s'.contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

(* pop_and_incorporate_context: result has non-empty contexts when starting ≥ 2 *)
Theorem pop_incorporate_contexts_ne:
  s.contexts ≠ [] ∧ 1 < LENGTH s.contexts ∧
  pop_and_incorporate_context success s = (INL (), s') ⇒
  s'.contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

(* handle_ex_helper preserves snc *)
Theorem handle_ex_helper_snc:
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (handle_ex_helper e s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* handle_exception preserves snc *)
Theorem handle_exception_snc:
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (handle_exception e s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* Additional ctx_pres building blocks for non-cp primitives *)
Theorem ctx_pres_more_leaves[simp]:
  ctx_pres (push_logs ls) ∧
  ctx_pres (add_to_delete a) ∧
  ctx_pres (set_tStorage x)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Guarded step_inst ops are ctx_pres *)
Theorem ctx_pres_step_inst_guarded[simp]:
  ctx_pres (step_sstore transient) ∧
  ctx_pres (step_log n) ∧
  ctx_pres step_self_destruct
Proof
  cheat  (* SCAFFOLD *)
QED

(* push_context preserves snc when pushed context satisfies snc predicate *)
Theorem push_context_snc[local]:
  snc s ∧ (c.msgParams.static ⇒ ∀a. c.msgParams.outputTo ≠ Code a) ⇒
  snc (SND (push_context (c, rb) s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* ctx_pres preserves contexts≠[] *)
Theorem ctx_pres_contexts_ne:
  ctx_pres m ∧ m s = (q, r) ∧ s.contexts ≠ [] ⇒ r.contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

(* step_inst preserves contexts ≠ [] — proved by expansion for create/call *)
Theorem proceed_create_contexts_ne[local]:
  s.contexts ≠ [] ⇒
  (SND (proceed_create sAddr addr v code gas s)).contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_call_contexts_ne[local]:
  s.contexts ≠ [] ⇒
  (SND (proceed_call op sender addr v aOff aSz code stip outTo s)).contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

(* === Combined snc + contexts≠[] composition (sne = snc ∧ ne) === *)
(* These thread BOTH properties through bind chains simultaneously.
   The conjunction avoids the negation issue that plagued separate ne_step. *)

Theorem sne_bind_cp[local]:
  cp g ∧
  (∀x s. snc s ∧ s.contexts ≠ [] ⇒
    snc (SND (f x s)) ∧ (SND (f x s)).contexts ≠ []) ∧
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (bind g f s)) ∧ (SND (bind g f s)).contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem sne_ignore_bind_cp[local]:
  cp g ∧
  (∀s. snc s ∧ s.contexts ≠ [] ⇒
    snc (SND (f s)) ∧ (SND (f s)).contexts ≠ []) ∧
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (ignore_bind g f s)) ∧ (SND (ignore_bind g f s)).contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem sne_let[local]:
  (∀x. snc (SND (f x s)) ∧ (SND (f x s)).contexts ≠ []) ⇒
  snc (SND ((let x = v in f x) s)) ∧
  (SND ((let x = v in f x) s)).contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem sne_cond[local]:
  (snc (SND (f1 s)) ∧ (SND (f1 s)).contexts ≠ []) ∧
  (snc (SND (f2 s)) ∧ (SND (f2 s)).contexts ≠ []) ⇒
  snc (SND ((if b then f1 else f2) s)) ∧
  (SND ((if b then f1 else f2) s)).contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem sne_uncurry[local]:
  (∀a b. snc (SND (f a b s)) ∧ (SND (f a b s)).contexts ≠ []) ⇒
  snc (SND (UNCURRY f p s)) ∧ (SND (UNCURRY f p s)).contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem sne_let_uncurry[local]:
  (∀a b. snc (SND (f a b s)) ∧ (SND (f a b s)).contexts ≠ []) ⇒
  snc (SND (LET (UNCURRY (λa b. f a b)) v s)) ∧
  (SND (LET (UNCURRY (λa b. f a b)) v s)).contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem sne_case_option[local]:
  (snc (SND (f_none s)) ∧ (SND (f_none s)).contexts ≠ []) ∧
  (∀x. snc (SND (f_some x s)) ∧ (SND (f_some x s)).contexts ≠ []) ⇒
  snc (SND ((case opt of NONE => f_none | SOME x => f_some x) s)) ∧
  (SND ((case opt of NONE => f_none | SOME x => f_some x) s)).contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ctx_pres_contexts_ne_snd[local]:
  ctx_pres m ∧ s.contexts ≠ [] ⇒ (SND (m s)).contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

(* sne step tactic: decompose monadic chain preserving snc ∧ contexts≠[] *)
val sne_solve = simp[] ORELSE first_assum ACCEPT_TAC;

(* strip_pos: strip ∀ and ⇒ without touching ∧ or ¬ *)
val strip_pos = rpt gen_tac >> rpt disch_tac;

val sne_one =
  (irule sne_uncurry >> strip_pos)
  ORELSE (irule sne_bind_cp >> TRY sne_solve
          >> TRY (simp[pairTheory.FORALL_PROD] >> strip_pos))
  ORELSE (irule sne_ignore_bind_cp >> TRY sne_solve
          >> TRY strip_pos)
  ORELSE (irule sne_let_uncurry >> TRY strip_pos)
  ORELSE (irule sne_let >> TRY strip_pos)
  ORELSE (irule sne_case_option >> TRY strip_pos)
  ORELSE (irule sne_cond >> conj_tac)
  ORELSE sne_solve;

(* Apply sne_one to current goal repeatedly *)
val sne_step = rpt (CHANGED_TAC sne_one);

(* Threading snc through a ctx_pres bind *)
Theorem snc_bind_ctx_pres:
  ctx_pres m ∧ snc s ∧ s.contexts ≠ [] ∧
  (∀x s'. m s = (INL x, s') ∧ snc s' ∧ s'.contexts ≠ [] ⇒
    snc (SND (f x s'))) ⇒
  snc (SND (bind m f s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* proceed_call with Memory outputTo preserves snc *)
Theorem proceed_call_snc[local]:
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (proceed_call op sender address value
    argsOff argsSize code stipend (Memory mr) s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* proceed_create preserves snc: pushed context has static=F *)
Theorem set_last_accounts_every_fst:
  ∀P a ls. ls ≠ [] ⇒
    (EVERY (λ(c,r). P c) (set_last_accounts a ls) ⇔
     EVERY (λ(c,r). P c) ls)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_create_snc[local]:
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (proceed_create senderAddr address value code cappedGas s))
Proof
  cheat  (* SCAFFOLD *)
QED


Theorem ctx_pres_abort_create_exists[local]:
  ctx_pres (abort_create_exists sAddr)
Proof
  cheat  (* SCAFFOLD *)
QED

(* snc/ne terminal for individual conjuncts *)
val snc_ne_hints =
  [cp_abort_unuse, cp_abort_call_value,
   cp_is_ctx_pres, ctx_pres_abort_create_exists];

val snc_term =
  (irule proceed_create_snc
   ORELSE irule proceed_call_snc
   ORELSE irule ctx_pres_preserves_snc)
  >> simp snc_ne_hints;

val ne_term =
  FIRST [irule proceed_create_contexts_ne >> simp snc_ne_hints,
         irule proceed_call_contexts_ne >> simp snc_ne_hints,
         irule ctx_pres_contexts_ne_snd >> simp snc_ne_hints];

(* solve_term: close snc or ne terminal goals *)
val solve_term =
  TRY (snc_term >> NO_TAC)
  >> TRY (ne_term >> NO_TAC)
  >> TRY (IF_CASES_TAC >> rpt conj_tac
          >> TRY (snc_term >> NO_TAC)
          >> TRY (ne_term >> NO_TAC));

(* Combined cp/ctx_pres sne: both snc and ne in one irule target *)
Theorem cp_sne[local]:
  cp m ∧ snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (m s)) ∧ (SND (m s)).contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_sne_pair[local]:
  cp m ∧ snc s ∧ s.contexts ≠ [] ∧ m s = (r, s') ⇒
  snc s' ∧ s'.contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ctx_pres_sne[local]:
  ctx_pres m ∧ snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (m s)) ∧ (SND (m s)).contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

(* Combined step_create: snc ∧ contexts≠[] *)
Theorem step_create_sne[local]:
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (step_create two s)) ∧
  (SND (step_create two s)).contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

(* Inner block of step_call after the first conditional *)
Theorem step_call_inner_sne[local]:
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (do
    set_return_data [];
    sucDepth <- get_num_contexts;
    if sucDepth > 1024 then abort_unuse b
    else proceed_call op sender addr value_arg args_off args_size code stipend
           (Memory mr)
  od s)) ∧
  (SND (do
    set_return_data [];
    sucDepth <- get_num_contexts;
    if sucDepth > 1024 then abort_unuse b
    else proceed_call op sender addr value_arg args_off args_size code stipend
           (Memory mr)
  od s)).contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

(* Combined step_call: snc ∧ contexts≠[] *)
Theorem step_call_sne[local]:
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (step_call op s)) ∧
  (SND (step_call op s)).contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

(* Combined step_inst: snc AND contexts≠[] — SND version *)
Theorem step_inst_sne[local]:
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (step_inst op s)) ∧ (SND (step_inst op s)).contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

(* handle_step preserves snc *)
Theorem handle_step_snc:
  snc s ∧ s.contexts ≠ [] ⇒
  snc (SND (handle_step e s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* Inner step of step preserves snc AND contexts ≠ [] *)
Theorem inner_preserves_snc_pair[local]:
  snc s ∧ s.contexts = h::t ∧
  (do context <- get_current_context;
      case FLOOKUP context.msgParams.parsed context.pc of
      | SOME op => do step_inst op; inc_pc_or_jump op od
      | NONE =>
          if LENGTH context.msgParams.code ≤ context.pc then step_inst Stop
          else step_inst Invalid
  od) s = (r, s1) ⇒
  snc s1 ∧ s1.contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

(* step preserves snc *)
Theorem step_preserves_snc:
  snc s ⇒ snc (SND (step s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_tr_preserves_snc:
  ∀r s. snc s ⇒ snc (SND (run_tr (r, s)))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem static_not_code_preserved:
  ∀es result fs.
    run es = SOME (INR result, fs) ∧
    EVERY (λ(c,r). c.msgParams.static ⇒
      ∀a. c.msgParams.outputTo ≠ Code a) es.contexts ⇒
    EVERY (λ(c,r). c.msgParams.static ⇒
      ∀a. c.msgParams.outputTo ≠ Code a) fs.contexts
Proof
  cheat  (* SCAFFOLD *)
QED
