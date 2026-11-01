(* ==========================================================================
 * run_call storage preservation: slots not in final storageKeys are unchanged,
 * unless a CREATE cleared the storage of an account that was not yet created.
 * The invariant tracks txParams and rollback states reachable by revert.
 * ========================================================================== *)
Theory vfmRunCall
Ancestors
  combin pair option pred_set list rich_list sum
  arithmetic finite_map While vfmTypes vfmConstants
  vfmContext vfmState vfmExecution vfmExecutionProp
  vfmStoragePredicates vfmSameFrame vfmPreserves vfmStaticCalls
  vfmDecreasesGas vfmStepLength vfmHandleStep vfmRunWithinFrame
  vfmHeadStack vfmHeadGas vfmJumpDest vfmPreserves
Libs
  dep_rewrite BasicProvers

(* EIP-8037: the account-creation charge and its credit, and the create that
   aborts before it enters a child.  Each wraps a state-gas meter action, so
   `vfmSameFrame`'s `preserves_same_frame_state_gas_meter` and
   `vfmStoragePredicates`' `preserves_rollback_state_gas_meter` cover the
   bodies; these are the wrappers, named here because the charge and the
   credit are what the call/create prefixes below peel. *)

Theorem preserves_same_frame_charge_new_account[simp]:
  preserves_same_frame (charge_new_account charged)
Proof
  Cases_on `charged` >> rw[charge_new_account_def]
QED

Theorem preserves_same_frame_credit_new_account[simp]:
  preserves_same_frame (credit_new_account charged)
Proof
  Cases_on `charged` >> rw[credit_new_account_def]
QED

Theorem preserves_storage_charge_new_account[simp]:
  preserves_storage (charge_new_account charged)
Proof
  Cases_on `charged` >> rw[charge_new_account_def]
QED

Theorem preserves_storage_credit_new_account[simp]:
  preserves_storage (credit_new_account charged)
Proof
  Cases_on `charged` >> rw[credit_new_account_def]
QED

Theorem preserves_same_frame_abort_create[simp]:
  preserves_same_frame abort_create
Proof
  rw[abort_create_def]
QED

(* The head-gas instance for the charge: `charge_state_gas` either moves only
   `stateGasLeft` or spills the excess through `consume_gas`, so the head
   frame's `gasUsed` never falls.  (The matching head-stack instance is
   vfmHeadStack's `preserves_head_stack_state_gas_meter`; the credit is not
   monotone in `gasUsed`, so it has no instance here.) *)

Theorem preserves_head_gas_mono_charge_state_gas[simp]:
  preserves_head_gas_mono (charge_state_gas n)
Proof
  rw[preserves_head_gas_mono_def, preserves_def, head_gas_mono_rel_def,
     charge_state_gas_def, bind_def, get_current_context_def, return_def,
     fail_def, assert_def, set_current_context_def, ignore_bind_def,
     consume_gas_def, LET_THM]
  (* EIP-8037: unfolding the charge leaves its whole body in a hypothesis, a
     `case` whose branches are the two pool paths, so the frame the goal reads
     can only be reached by taking that hypothesis into the goal and splitting
     it there.  An empty stack fails before the body, which `Cases_on` settles
     with the charge's own guard in hand. *)
  >> Cases_on `s.contexts` >> gvs[]
  >> TRY (rpt (pop_assum mp_tac) >> rpt IF_CASES_TAC >> rpt disch_tac
          >> gvs[consume_gas_def, get_current_context_def,
                 set_current_context_def, charge_state_gas_def,
                 assert_def, bind_def, ignore_bind_def, return_def,
                 fail_def, LET_THM, AllCaseEqs(),
                 pairTheory.PAIR_FST_SND_EQ, APPLY_UPDATE_THM]
          >> rw[] >> NO_TAC)
  >> rpt (gvs[AllCaseEqs()] >> decide_tac)
QED

Theorem preserves_head_gas_mono_charge_new_account[simp]:
  preserves_head_gas_mono (charge_new_account charged)
Proof
  Cases_on `charged` >> rw[charge_new_account_def]
QED

(* Saved frames can revert down to the entry frame, but never the root. *)
Definition active_rollbacks_def:
  active_rollbacks es_depth s =
    s.rollback ::
    MAP SND (TAKE (SUC (LENGTH s.contexts) - MAX 2 es_depth) s.contexts)
End

Theorem active_rollbacks_saved:
  active_rollbacks es_depth s =
    s.rollback ::
    (if LENGTH s.contexts < es_depth then []
     else MAP SND (TAKE (MIN (LENGTH s.contexts - es_depth + 1)
                              (LENGTH s.contexts - 1)) s.contexts))
Proof
  Cases_on `LENGTH s.contexts < es_depth`
  >- (`SUC (LENGTH s.contexts) - MAX 2 es_depth = 0`
      by (rw[MAX_DEF] >> decide_tac)
      >> simp[active_rollbacks_def])
  >> `SUC (LENGTH s.contexts) - MAX 2 es_depth =
        MIN (LENGTH s.contexts - es_depth + 1) (LENGTH s.contexts - 1)`
     by (rw[MAX_DEF, MIN_DEF] >> decide_tac)
  >> simp[active_rollbacks_def]
QED

Theorem active_rollbacks_set_original[simp]:
  active_rollbacks n (SND (set_original a s)) = active_rollbacks n s
Proof
  rw[set_original_def, return_def, fail_def, active_rollbacks_def]
QED

(* Per-context outputTo consistency, needed across pops. *)

Theorem outputTo_consistent_stack_imp_consistent:
  outputTo_consistent_stack s ⇒ outputTo_consistent s
Proof
  rw[outputTo_consistent_stack_def, outputTo_consistent_def]
  >> Cases_on `s.contexts` >> gvs[outputTo_consistent_ctx_def]
QED

(* Per-slot storage preservation outside access-listed storage keys. *)

Definition storage_slot_preserved_def:
  storage_slot_preserved rb rb0 ⇔
    ∀a k. ¬fIN (SK a k) rb.accesses.storageKeys ⇒
        lookup_storage k (lookup_account a rb.accounts).storage =
        lookup_storage k (lookup_account a rb0.accounts).storage
End

(* -------------------------------------------------------------------------
 * The 2-state run_call invariant.
 * ------------------------------------------------------------------------- *)

(* Note: CREATE now clears the storage of the address it creates (as EELS
   process_create_message does) without adding its slots to storageKeys, so
   storage_slot_preserved no longer holds for the active rollbacks. One
   invariant that does hold: for each active rollback rb, a slot outside
   rb's storageKeys either equals its value in es.rollback, or is 0w and the
   account had nonce 0 and no code in es.rollback. Creation sets the nonce
   to 1, and the invariant also tracks that an account created in es.rollback
   stays created in the current rollback and in every saved rollback above
   es. *)
Definition run_call_inv_def:
  run_call_inv es (q:unit + exception option) s ⇔
    s.txParams = es.txParams ∧
    outputTo_consistent_stack s ∧
    wf_state s ∧
    EVERY (λrb. ∀a k. ¬fIN (SK a k) rb.accesses.storageKeys ⇒
      lookup_storage k (lookup_account a rb.accounts).storage =
        lookup_storage k (lookup_account a es.rollback.accounts).storage ∨
      lookup_storage k (lookup_account a rb.accounts).storage = 0w ∧
        ¬account_already_created (lookup_account a es.rollback.accounts))
      (active_rollbacks (LENGTH es.contexts) s) ∧
    (ISL q ∧ LENGTH es.contexts ≤ LENGTH s.contexts ⇒
      EVERY (λrb. ∀a.
        account_already_created (lookup_account a es.rollback.accounts) ⇒
        account_already_created (lookup_account a rb.accounts))
        (s.rollback :: MAP SND
          (TAKE (LENGTH s.contexts - LENGTH es.contexts) s.contexts)) ∧
      EVERY (λmp. ∀a. mp.outputTo = Code a ⇒
        ¬account_already_created (lookup_account a es.rollback.accounts))
        (MAP (λp. (FST p).msgParams)
          (TAKE (LENGTH s.contexts - LENGTH es.contexts) s.contexts)))
End

(* -------------------------------------------------------------------------
 * Reflexivity.
 * ------------------------------------------------------------------------- *)

Theorem run_call_inv_refl:
  wf_state es ∧
  (FST (HD es.contexts)).jumpDest = NONE ∧
  EVERY (λrb. storage_slot_preserved rb es.rollback)
        (MAP SND (TAKE 2 es.contexts)) ⇒
  run_call_inv es (INL ()) es
Proof
  rw[run_call_inv_def, active_rollbacks_saved, storage_slot_preserved_def]
  >> gvs[outputTo_consistent_stack_def,wf_state_def]
  >> Cases_on `es.contexts` >> gvs[]
  >> rw[MIN_DEF]
  >> Cases_on`t` >> gvs[ADD1]
QED

(* Single-step preservation of run_call_inv: split on same-frame/push/pop. *)


(* Same-frame step storage preservation outside final storageKeys. *)

(* Same-frame case: non-callee storage is unchanged by callee_local_changes;
 * callee storage can change only via SSTORE, which first access-lists the slot. *)



(* Pushed rollback storage: when CALL/CREATE pushes, the new head's saved
 * rollback has the old rollback's storage. *)

(* proceed_call captures s.rollback as the pushed rollback. *)
Theorem proceed_call_push_structure:
  proceed_call op sender address value argsOffset argsSize code stipend
               outputTo s = (r, s') ∧ s.contexts ≠ [] ⇒
  LENGTH s'.contexts = LENGTH s.contexts + 1 ∧
  TL (TL s'.contexts) = TL s.contexts ∧
  FST (HD (TL s'.contexts)) =
    (FST (HD s.contexts) with stateGasLeft := 0) ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet s'.rollback.accesses.storageKeys ∧
  (FST (HD s'.contexts)).msgParams.outputTo = outputTo ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet (SND (HD s'.contexts)).accesses.storageKeys
Proof
  strip_tac >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h`
  >> qhdtm_x_assum `proceed_call` mp_tac
  >> simp[proceed_call_def, drain_state_gas_reservoir_def,
          bind_def, ignore_bind_def, get_current_context_def,
          set_current_context_def, return_def, get_rollback_def,
          read_memory_def, get_caller_def, get_value_def, get_static_def,
          get_accounts_def]
  >> Cases_on `op <> CallCode /\ 0 < value`
  >> (simp[update_accounts_def, return_def]
  >> simp[push_context_def, return_def, bind_def]
  >> qmatch_goalsub_abbrev_tac `(if _ then _ else _) ss`
  >> Cases_on `fIN address precompile_addresses`
  >- (simp[] >> strip_tac
      >> `ss.contexts <> []` by simp[Abbr`ss`]
      >> qmatch_asmsub_abbrev_tac `dpa ss = (_, _)`
      >> `preserves_same_frame dpa` by simp[Abbr`dpa`]
      >> pop_assum mp_tac
      >> rewrite_tac[preserves_same_frame_def]
      >> disch_then drule >> simp[]
      >> simp[same_frame_rel_def, Abbr`ss`]
      >> strip_tac >> gvs[initial_context_def, initial_msg_params_def])
  >> simp[return_def, Abbr`ss`, initial_context_def, initial_msg_params_def]
  >> strip_tac >> gvs[])
QED

Theorem proceed_call_saved_parent_rollback:
  proceed_call op sender address value argsOffset argsSize code stipend
               outputTo s = (r, s') ∧ s.contexts ≠ [] ⇒
  SND (HD (TL s'.contexts)) = SND (HD s.contexts)
Proof
  strip_tac >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h`
  >> qhdtm_x_assum `proceed_call` mp_tac
  >> simp[proceed_call_def, drain_state_gas_reservoir_def,
          bind_def, ignore_bind_def, get_current_context_def,
          set_current_context_def, return_def, get_rollback_def,
          read_memory_def, get_caller_def, get_value_def, get_static_def,
          get_accounts_def]
  >> Cases_on `op <> CallCode /\ 0 < value`
  >> (simp[update_accounts_def, return_def, push_context_def, bind_def]
      >> qmatch_goalsub_abbrev_tac `(if _ then _ else _) ss`
      >> Cases_on `fIN address precompile_addresses`
      >- (simp[] >> strip_tac
          >> `ss.contexts <> []` by simp[Abbr`ss`]
          >> qmatch_asmsub_abbrev_tac `dpa ss = (_, _)`
          >> `preserves_same_frame dpa` by simp[Abbr`dpa`]
          >> pop_assum mp_tac
          >> rewrite_tac[preserves_same_frame_def]
          >> disch_then drule >> simp[]
          >> simp[same_frame_rel_def, Abbr`ss`]
          >> strip_tac >> gvs[])
      >> simp[return_def, Abbr`ss`] >> strip_tac >> gvs[])
QED

Theorem proceed_create_push_structure:
  proceed_create senderAddress address value code cappedGas s = (r, s') ∧
  s.contexts ≠ [] ⇒
  LENGTH s'.contexts = LENGTH s.contexts + 1 ∧
  TL (TL s'.contexts) = TL s.contexts ∧
  FST (HD (TL s'.contexts)) =
    (FST (HD s.contexts) with stateGasLeft := 0) ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet s'.rollback.accesses.storageKeys ∧
  outputTo_consistent_ctx (FST (HD s'.contexts)) ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet (SND (HD s'.contexts)).accesses.storageKeys
Proof
  strip_tac
  >> qhdtm_x_assum `proceed_create` mp_tac
  >> simp[proceed_create_def, drain_state_gas_reservoir_def,
          get_current_context_def, set_current_context_def,
          bind_def, ignore_bind_def, return_def, get_accounts_def]
  >> simp[ignore_bind_def, Once bind_def, update_accounts_def, return_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_rollback_def, return_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_original_def, return_def, fail_def]
  >> rewrite_tac[Once bind_def]
  >> simp[set_original_def, return_def, fail_def]
  >> rewrite_tac[Once bind_def]
  >> simp[update_accounts_def, return_def]
  >> strip_tac
  >> drule push_context_effect >> strip_tac >> gvs[]
  >> simp[outputTo_consistent_ctx_def, initial_context_def,
          initial_msg_params_def]
  >> simp[set_last_accounts_def, MAP_SNOC, MAP_FRONT]
  >> Cases_on `s.contexts` >> gvs[SUBSET_DEF]
QED

Theorem proceed_create_saved_parent_rollback:
  proceed_create senderAddress address value code cappedGas s = (r, s') ∧
  s.contexts ≠ [] ⇒
  SND (HD (TL s'.contexts)) = SND (HD s.contexts)
Proof
  strip_tac
  >> qhdtm_x_assum `proceed_create` mp_tac
  >> simp[proceed_create_def, drain_state_gas_reservoir_def,
          get_current_context_def, set_current_context_def,
          bind_def, ignore_bind_def, return_def, update_accounts_def,
          get_rollback_def, get_original_def, set_original_def, fail_def,
          push_context_def, get_accounts_def]
  >> strip_tac >> gvs[]
QED

Theorem proceed_call_pushed_rb_storage:
  proceed_call op sender address value argsOffset argsSize code stipend
                outputTo s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  ∀a. (lookup_account a (SND (HD s'.contexts)).accounts).storage =
      (lookup_account a s.rollback.accounts).storage
Proof
  strip_tac >> Cases_on `s.contexts` >> gvs[]
  >> PairCases_on `h`
  >> qhdtm_x_assum `proceed_call` mp_tac
  >> simp[proceed_call_def, drain_state_gas_reservoir_def,
          bind_def, ignore_bind_def, get_current_context_def,
          set_current_context_def, return_def, get_rollback_def,
          read_memory_def, get_caller_def, get_value_def, get_static_def,
          get_accounts_def]
  >> Cases_on `op <> CallCode /\ 0 < value`
  >> (simp[update_accounts_def, return_def, push_context_def, bind_def]
      >> qmatch_goalsub_abbrev_tac `(if _ then _ else _) ss`
      >> Cases_on `fIN address precompile_addresses`
      >- (simp[] >> strip_tac
          >> `ss.contexts <> []` by simp[Abbr`ss`]
          >> qmatch_asmsub_abbrev_tac `dpa ss = (_, _)`
          >> `preserves_same_frame dpa` by simp[Abbr`dpa`]
          >> pop_assum mp_tac
          >> rewrite_tac[preserves_same_frame_def]
          >> disch_then drule >> simp[]
          >> simp[same_frame_rel_def, Abbr`ss`]
          >> strip_tac >> gvs[])
      >> simp[return_def, Abbr`ss`] >> strip_tac >> gvs[])
QED

(* Intermediate: proceed_create captures s.rollback (post increment_nonce)
   as the pushed rollback. increment_nonce and set_original do not touch
   s.rollback.accounts.storage. transfer_value happens AFTER get_rollback,
   so it doesn't affect the captured rollback. *)
Theorem proceed_create_pushed_rb_storage:
  proceed_create senderAddress address value code cappedGas s = (r, s') ∧
  s.contexts ≠ [] ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
  ∀a. (lookup_account a (SND (HD s'.contexts)).accounts).storage =
      (lookup_account a s.rollback.accounts).storage
Proof
  strip_tac
  >> qhdtm_x_assum `proceed_create` mp_tac
  >> simp[proceed_create_def, drain_state_gas_reservoir_def,
          get_current_context_def, set_current_context_def,
          bind_def, ignore_bind_def, return_def, get_accounts_def]
  (* update_accounts (increment_nonce senderAddress) *)
  >> simp[ignore_bind_def, Once bind_def, update_accounts_def, return_def]
  (* get_rollback: captures increment_nonce'd rollback. *)
  >> rewrite_tac[Once bind_def]
  >> simp[get_rollback_def, return_def]
  (* get_original / set_original: don't modify s.rollback. *)
  >> rewrite_tac[Once bind_def]
  >> simp[get_original_def, return_def, fail_def]
  >> rewrite_tac[Once bind_def]
  >> simp[set_original_def, return_def, fail_def]
  (* update_accounts (transfer_value o increment_nonce): modifies s.rollback,
     but the captured `rollback` variable already holds the pre-transfer one. *)
  >> rewrite_tac[Once bind_def]
  >> simp[update_accounts_def, return_def]
  (* push_context. *)
  >> strip_tac
  >> drule push_context_effect >> strip_tac >> gvs[]
  (* After push: HD s'.contexts = (ctx, rollback-with-incremented-nonce).
     increment_nonce preserves storage at every address. *)
  >> rw[lookup_account_def, increment_nonce_def,
        combinTheory.APPLY_UPDATE_THM, finite_mapTheory.FLOOKUP_UPDATE]
  >> gvs[update_account_def, APPLY_UPDATE_THM]
  >> rw[]
QED

(* proceed_call push structure.

   EIP-8037: the call drains the calling frame's reservoir before it
   pushes.  `drain_state_gas_reservoir` (`spec/vfmExecutionScript.sml:653`)
   sets the current context's `stateGasLeft := 0` and returns the old
   value, `proceed_call_def` (`:1798`) opens with it and builds the new
   frame from that return (`:1822`), and `push_context` (`:270`) is
   `contexts updated_by CONS crb`.  So the output's tail is the parent
   *with its reservoir zeroed*, and the tail equality holds only of the
   frames below the parent; the parent's one moved field is named here.
   Checked witness for the old form:
   `spec/prop/vfmCallDrainProbeScript.sml`
   `proceed_call_push_structure_counterexample`. *)

(* CALL/CREATE wrappers: same-frame storage-preserving prefixes, then proceed_*. *)

(* Composable predicate: if m grows, the pushed rollback preserves storage. *)
Definition preserves_pushed_rb_storage_def:
  preserves_pushed_rb_storage (m : α execution) ⇔
    ∀s r s'. m s = (r, s') ∧ s.contexts ≠ [] ∧
             LENGTH s'.contexts > LENGTH s.contexts ⇒
      ∀a. (lookup_account a (SND (HD s'.contexts)).accounts).storage =
          (lookup_account a s.rollback.accounts).storage
End

(* Same-frame prefixes cannot grow, so the pushed-rb property is vacuous. *)
Theorem preserves_pushed_rb_storage_of_same_frame[simp]:
  preserves_same_frame m ⇒ preserves_pushed_rb_storage m
Proof
  rw[preserves_same_frame_def, preserves_pushed_rb_storage_def]
  >> first_x_assum drule >> simp[same_frame_rel_def]
QED

(* bind composition for pushed-rb storage. *)
Theorem preserves_pushed_rb_storage_bind:
  preserves_storage g ∧ preserves_same_frame g ∧
  (∀x. preserves_pushed_rb_storage (f x)) ⇒
  preserves_pushed_rb_storage (bind g f)
Proof
  rw[preserves_pushed_rb_storage_def, bind_def]
  >> gvs[AllCaseEqs()]
  >> fs[preserves_storage_def, preserves_same_frame_def]
  >> rpt (first_x_assum drule) >> simp[same_frame_rel_def] >> strip_tac
  >> rpt strip_tac
  (* s_mid has same contexts and storage as s. *)
  >> qmatch_asmsub_rename_tac `g s = (_, s_mid)`
  >> `s_mid.contexts ≠ []` by (Cases_on `s.contexts` >> Cases_on `s_mid.contexts` >> fs[])
  >> `LENGTH s'.contexts > LENGTH s_mid.contexts` by fs[]
  >> first_x_assum drule >> simp[]
  >> disch_then (qspec_then `a` mp_tac) >> simp[]
  >> gvs[lookup_storage_def, FUN_EQ_THM]
QED

Theorem preserves_pushed_rb_storage_ignore_bind:
  preserves_storage g ∧ preserves_same_frame g ∧
  preserves_pushed_rb_storage f ⇒
  preserves_pushed_rb_storage (ignore_bind g f)
Proof
  rw[ignore_bind_def]
  >> irule preserves_pushed_rb_storage_bind >> rw[]
QED

Theorem preserves_pushed_rb_storage_cond[simp]:
  preserves_pushed_rb_storage m1 ∧ preserves_pushed_rb_storage m2 ⇒
  preserves_pushed_rb_storage (if b then m1 else m2)
Proof
  rw[]
QED

(* Base case: proceed_call preserves pushed rb storage. *)
Theorem preserves_pushed_rb_storage_proceed_call[simp]:
  preserves_pushed_rb_storage
    (proceed_call op sender address value argsOffset argsSize
                  code stipend outputTo)
Proof
  rw[preserves_pushed_rb_storage_def]
  >> drule_all proceed_call_pushed_rb_storage
  >> simp[]
QED

Theorem preserves_pushed_rb_storage_proceed_create[simp]:
  preserves_pushed_rb_storage
    (proceed_create senderAddress address value code cappedGas)
Proof
  rw[preserves_pushed_rb_storage_def]
  >> drule_all proceed_create_pushed_rb_storage
  >> simp[]
QED

(* Now step_call = a bunch of preserves_storage+preserves_same_frame
   primitives followed by either abort_call_value (which is
   preserves_same_frame, vacuously preserves_pushed_rb_storage),
   abort_unuse (likewise), or proceed_call. *)
Theorem preserves_pushed_rb_storage_step_call[simp]:
  preserves_pushed_rb_storage (step_call op)
Proof
  simp[step_call_def]
  (* Shape mirrors preserves_storage_step_call's proof. Every bind
     prefix is preserves_storage + preserves_same_frame; use the
     bind rule with those two side conditions. *)
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> pairarg_tac >> simp[]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[]
  >> reverse conj_tac >- (CASE_TAC >> simp[])
  >> Cases >> simp[]
  (* EIP-8037: the opcode's execution gas, the creation charge in state
     gas, the static check and the memory expansion come before the
     child's grant is read. *)
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> pairarg_tac >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_cond >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_cond >> simp[]
QED

(* abort_create_exists doesn't grow contexts, so vacuously preserves
   pushed-rb storage. Unlike abort_call_value/abort_unuse, it is NOT
   unconditionally preserves_same_frame (it requires the sender address
   to match the current callee), so we prove it from the length lemma. *)
Theorem preserves_pushed_rb_storage_abort_create_exists[simp]:
  preserves_pushed_rb_storage (abort_create_exists a)
Proof
  rw[preserves_pushed_rb_storage_def]
  >> drule_all abort_create_exists_length
  >> simp[]
QED

Theorem preserves_pushed_rb_storage_step_create[simp]:
  preserves_pushed_rb_storage (step_create two)
Proof
  simp[step_create_def]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> rpt (irule preserves_pushed_rb_storage_ignore_bind >> simp[])
  >> irule preserves_pushed_rb_storage_bind >> simp[] >> gen_tac
  >> irule preserves_pushed_rb_storage_cond >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  (* EIP-8037: the destination's creation is charged in state gas before
     the child's grant is withheld, so a spill thins what is withheld. *)
  >> irule preserves_pushed_rb_storage_ignore_bind >> simp[]
  >> irule preserves_pushed_rb_storage_bind
  >> simp[preserves_same_frame_state_gas_meter] >> gen_tac
  >> irule preserves_pushed_rb_storage_cond >> simp[]
QED

(* Final user-facing lemmas. *)
Theorem step_call_pushed_rb_storage:
  ∀op s r s'. step_call op s = (r, s') ∧ s.contexts ≠ [] ∧
    LENGTH s'.contexts > LENGTH s.contexts ⇒
    ∀a. (lookup_account a (SND (HD s'.contexts)).accounts).storage =
        (lookup_account a s.rollback.accounts).storage
Proof
  metis_tac[preserves_pushed_rb_storage_step_call,
            preserves_pushed_rb_storage_def]
QED

Theorem step_create_pushed_rb_storage:
  ∀two s r s'. step_create two s = (r, s') ∧ s.contexts ≠ [] ∧
    LENGTH s'.contexts > LENGTH s.contexts ⇒
    ∀a. (lookup_account a (SND (HD s'.contexts)).accounts).storage =
        (lookup_account a s.rollback.accounts).storage
Proof
  metis_tac[preserves_pushed_rb_storage_step_create,
            preserves_pushed_rb_storage_def]
QED

(* step_call growth structure: peel same-frame prefixes, then proceed_call. *)
Theorem step_call_push_structure:
  step_call op s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  TL (TL s'.contexts) = TL s.contexts ∧
  SND (HD (TL s'.contexts)) = SND (HD s.contexts) ∧
  (FST (HD (TL s'.contexts))).msgParams = (FST (HD s.contexts)).msgParams ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet s'.rollback.accesses.storageKeys ∧
  outputTo_consistent_ctx (FST (HD s'.contexts)) ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet (SND (HD s'.contexts)).accesses.storageKeys
Proof
  simp[step_call_def] >> strip_tac
  (* Peel pop_stack *)
  >> qmatch_asmsub_abbrev_tac`pop_stack n`
  >> `preserves_same_frame (pop_stack n)` by simp[]
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> pairarg_tac >> gvs[]
  >> `sm.contexts ≠ []` by (strip_tac >> gvs[same_frame_rel_def])
  >> `LENGTH sm.contexts = LENGTH s.contexts` by gvs[same_frame_rel_def]
  (* Peel memory_expansion_info *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ sm = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sm s2`
  >> `same_frame_rel s s2` by metis_tac[same_frame_rel_trans]
  >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel consume_gas *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s2 s3`
  >> `same_frame_rel s s3` by metis_tac[same_frame_rel_trans]
  >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel expand_memory *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s3 s4`
  >> `same_frame_rel s s4` by metis_tac[same_frame_rel_trans]
  >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s4 s5`
  >> `same_frame_rel s s5` by metis_tac[same_frame_rel_trans]
  >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> pairarg_tac >> gvs[ignore_bind_def]
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s5 s6`
  >> `same_frame_rel s s6` by metis_tac[same_frame_rel_trans]
  >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* EIP-8037: the creation charge, the static check and the memory
     expansion come before the child's grant is read. *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s6 sc`
  >> `same_frame_rel s sc` by metis_tac[same_frame_rel_trans]
  >> `sc.contexts ≠ [] ∧ LENGTH sc.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sc s7`
  >> `same_frame_rel s s7` by metis_tac[same_frame_rel_trans]
  >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s7 s8`
  >> `same_frame_rel s s8` by metis_tac[same_frame_rel_trans]
  >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* The grant is computed after the charge, so the 63/64 rule sees the
     execution gas a spill thinned. *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s8 sd`
  >> `same_frame_rel s sd` by metis_tac[same_frame_rel_trans]
  >> `sd.contexts ≠ [] ∧ LENGTH sd.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> pairarg_tac >> gvs[ignore_bind_def]
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sd s9`
  >> `same_frame_rel s s9` by metis_tac[same_frame_rel_trans]
  >> `s9.contexts ≠ [] ∧ LENGTH s9.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel get_callee *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s9 s0`
  >> `same_frame_rel s s0` by metis_tac[same_frame_rel_trans]
  >> `s0.contexts ≠ [] ∧ LENGTH s0.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
  >> gvs[Ntimes COND_RATOR 2]
  >> Cases_on`bbb` >> gs[]
  >- (
    drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved
    >> simp[])
  (* Peel set_return_data via ignore_bind *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s0 sa`
  >> `same_frame_rel s sa` by metis_tac[same_frame_rel_trans]
  >> `sa.contexts ≠ [] ∧ LENGTH sa.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel get_num_contexts *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sa sb`
  >> `same_frame_rel s sb` by metis_tac[same_frame_rel_trans]
  >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Now at the conditional: if value check then abort else continue *)
  (* Second conditional: if depth/code check then abort else proceed_call *)
  >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
  >> gvs[COND_RATOR]
  >> Cases_on`bbb` >> gs[]
  >- (
    drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved
    >> simp[])
  (* Now we have proceed_call sm = (_, s') with growth, and same_frame_rel s sm *)
  >> drule_all_then assume_tac proceed_call_saved_parent_rollback
  >> drule_all proceed_call_push_structure
  >> strip_tac
  (* The prefix preserves the parent's saved rollback and msgParams. *)
  >> `TL sb.contexts = TL s.contexts` by ( fs[same_frame_rel_def] )
  >> gvs[]
  >> conj_asm1_tac >- gvs[same_frame_rel_def]
  >> conj_asm1_tac >- gvs[same_frame_rel_def]
  >> conj_tac >- metis_tac[SUBSET_TRANS, same_frame_rel_def]
  (* outputTo_consistent: outputTo = Memory from step_call, so Code a is vacuous *)
  >> conj_tac >- simp[outputTo_consistent_ctx_def]
  >> metis_tac[SUBSET_TRANS, same_frame_rel_def]
QED

(* TODO: move *)
Theorem LAST_CONS_SNOC:
  LAST (x::(SNOC y z)) = y
Proof
  map_every qid_spec_tac[`x`,`y`,`z`] >> Induct >> rw[]
QED

(* TODO: move *)
Theorem FRONT_CONS_SNOC:
  FRONT (x::(SNOC y z)) = x::z
Proof
  map_every qid_spec_tac[`x`,`y`,`z`] >> Induct >> rw[] >>
  rewrite_tac[GSYM SNOC_APPEND] >> rw[]
QED

(* step_create growth structure. set_original updates originalAccounts
 * and leaves saved rollback pairs unchanged. *)
Theorem step_create_push_structure:
  step_create two s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  MAP FST (TL (TL s'.contexts)) = MAP FST (TL s.contexts) ∧
  (∀i. i < LENGTH s.contexts ⇒
       (SND (EL i (TL s'.contexts))).accesses = (SND (EL i s.contexts)).accesses) ∧
  (FST (HD (TL s'.contexts))).msgParams = (FST (HD s.contexts)).msgParams ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet s'.rollback.accesses.storageKeys ∧
  outputTo_consistent_ctx (FST (HD s'.contexts)) ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet (SND (HD s'.contexts)).accesses.storageKeys ∧
  (∀a. a ≠ (FST (HD s'.contexts)).msgParams.callee ⇒
     (lookup_account a (SND (HD (TL s'.contexts))).accounts).storage =
     (lookup_account a (SND (HD s.contexts)).accounts).storage) ∧
  (∀i. i < LENGTH s.contexts - 1 ⇒
     (SND (EL i (TL s'.contexts))).accounts =
     (SND (EL i s.contexts)).accounts) ∧
  (∀a. a ≠ (FST (HD s'.contexts)).msgParams.callee ⇒
    (lookup_account a (SND (EL (LENGTH s.contexts) s'.contexts)).accounts).storage =
    (lookup_account a (SND (LAST s.contexts)).accounts).storage)
Proof
  simp[step_create_def] >> strip_tac
  (* Peel pop_stack *)
  >> qmatch_asmsub_abbrev_tac`pop_stack n`
  >> `preserves_same_frame (pop_stack n)` by simp[]
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> `sm.contexts ≠ []` by (strip_tac >> gvs[same_frame_rel_def])
  >> `LENGTH sm.contexts = LENGTH s.contexts` by gvs[same_frame_rel_def]
  (* Peel memory_expansion_info *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ sm = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sm s2`
  >> `same_frame_rel s s2` by metis_tac[same_frame_rel_trans]
  >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel consume_gas *)
  >> gvs[ignore_bind_def]
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s2 s3`
  >> `same_frame_rel s s3` by metis_tac[same_frame_rel_trans]
  >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel expand_memory *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s3 s4`
  >> `same_frame_rel s s4` by metis_tac[same_frame_rel_trans]
  >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel read_memory *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s4 s5`
  >> `same_frame_rel s s5` by metis_tac[same_frame_rel_trans]
  >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel get_callee *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s5 s6`
  >> `same_frame_rel s s6` by metis_tac[same_frame_rel_trans]
  >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel get_accounts *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s6 s7`
  >> `same_frame_rel s s7` by metis_tac[same_frame_rel_trans]
  >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel assert (code length) via ignore_bind *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s7 s8`
  >> `same_frame_rel s s8` by metis_tac[same_frame_rel_trans]
  >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel assert_not_static *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s8 s0`
  >> `same_frame_rel s s0` by metis_tac[same_frame_rel_trans]
  >> `s0.contexts ≠ [] ∧ LENGTH s0.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel set_return_data *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel s0 sa`
  >> `same_frame_rel s sa` by metis_tac[same_frame_rel_trans]
  >> `sa.contexts ≠ [] ∧ LENGTH sa.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel get_num_contexts *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sa sb`
  >> `same_frame_rel s sb` by metis_tac[same_frame_rel_trans]
  >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Split the preliminary failure condition. *)
  >> qmatch_asmsub_abbrev_tac`COND preliminaryFailure _ _ _ = (_, _)`
  >> gvs[COND_RATOR]
  >> qpat_x_assum`COND preliminaryFailure _ _ = _`mp_tac
  >> IF_CASES_TAC
  >- ((* abort_create: preserves_same_frame, can't grow *)
      strip_tac >>
      drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved
      >> simp[])
  >> strip_tac
  (* Peel access_address *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sb sd`
  >> `same_frame_rel s sd` by metis_tac[same_frame_rel_trans]
  >> `sd.contexts ≠ [] ∧ LENGTH sd.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel ensure_storage_in_domain *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sd sx`
  >> `same_frame_rel s sx` by metis_tac[same_frame_rel_trans]
  >> `sx.contexts ≠ [] ∧ LENGTH sx.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* EIP-8037: the destination's creation, charged before the child's
     grant is withheld so a spill thins what is withheld. *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sx sy`
  >> `same_frame_rel s sy` by metis_tac[same_frame_rel_trans]
  >> `sy.contexts ≠ [] ∧ LENGTH sy.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Peel withhold_create_gas *)
  >> drule_at (Pat`bind`) bind_psf_grows_extract
  >> simp[preserves_same_frame_state_gas_meter] >> qpat_x_assum`_ _ = (_,_)`kall_tac >> strip_tac >> gvs[]
  >> rename1`same_frame_rel sy se`
  >> `same_frame_rel s se` by metis_tac[same_frame_rel_trans]
  >> `se.contexts ≠ [] ∧ LENGTH se.contexts = LENGTH s.contexts`
  by (rpt strip_tac >> gvs[same_frame_rel_def])
  (* Now at the collision conditional. *)
  >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
  >> gvs[COND_RATOR]
  >> qpat_x_assum`COND bbb _ _ = _`mp_tac
  >> IF_CASES_TAC
  >- ((* abort_create_exists: length_preserves, can't grow *)
      strip_tac >>
      drule (REWRITE_RULE[length_preserves_def] length_preserves_abort_create_exists)
      >> simp[])
  (* Now we have proceed_create se = (_, s') with growth, and same_frame_rel s se *)
  >> strip_tac
  >> qpat_x_assum `s.contexts ≠ []` mp_tac
  >> qpat_x_assum `se.contexts ≠ []` mp_tac
  >> qpat_x_assum `same_frame_rel s se` mp_tac
  >> qpat_x_assum `proceed_create _ _ _ _ _ se = _` mp_tac
  >> POP_ASSUM_LIST (K all_tac)
  >> ntac 4 strip_tac
  >> drule_all_then assume_tac proceed_create_saved_parent_rollback
  >> drule_all proceed_create_push_structure >> strip_tac
  >> `TL se.contexts = TL s.contexts /\
      SND (HD se.contexts) = SND (HD s.contexts) /\
      (FST (HD se.contexts)).msgParams = (FST (HD s.contexts)).msgParams /\
      toSet s.rollback.accesses.storageKeys SUBSET toSet se.rollback.accesses.storageKeys`
     by fs[same_frame_rel_def]
  >> qpat_x_assum `same_frame_rel _ _` kall_tac
  >> qhdtm_x_assum `proceed_create` kall_tac
  >> Cases_on `s.contexts` >- gvs[]
  >> Cases_on `se.contexts` >- gvs[]
  >> Cases_on `s'.contexts` >- gvs[]
  >> Cases_on `t''` >- gvs[]
  >> gvs[]
  >> conj_tac >- (gen_tac >> Cases_on `i` >> simp[])
  >> conj_tac >- metis_tac[SUBSET_TRANS]
  >> conj_tac >- metis_tac[SUBSET_TRANS]
  >> conj_tac >- (gen_tac >> Cases_on `i` >> simp[])
  >> Cases_on `t` >> gvs[]
  >> simp[LAST_EL]
QED

Theorem handle_step_same_length_storageKeys_subset:
  outputTo_consistent s ∧
  handle_step e s = (r,s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  toSet s.rollback.accesses.storageKeys SUBSET
  toSet s'.rollback.accesses.storageKeys
Proof
  strip_tac >> drule_all handle_step_same_frame
  >> simp[same_frame_rel_def]
QED

(* Full step storage preservation in the same-frame case. *)
Theorem step_same_length_preserves_non_accessed_storage:
  ∀s r s'. step s = (r, s') ∧ s.contexts ≠ [] ∧
    outputTo_consistent s ∧
    LENGTH s'.contexts = LENGTH s.contexts ⇒
  ∀a k. ¬fIN (SK a k) s'.rollback.accesses.storageKeys ⇒
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  rpt gen_tac >> strip_tac
  >> drule_all step_same_frame
  >> simp[same_frame_rel_def]
  >> strip_tac
  >> rpt gen_tac >> strip_tac
  >> reverse (Cases_on `a = (FST (HD s.contexts)).msgParams.callee`)
  >- (
    (* Non-callee address: callee_local_changes gives equality directly. *)
    `(lookup_account a s'.rollback.accounts).storage =
     (lookup_account a s.rollback.accounts).storage`
       by fs[same_frame_rel_def, callee_local_changes_def]
    >> simp[])
  (* Callee address. Unfold step = handle inner handle_step and
     analyse the cases. *)
  >> `¬fIN (SK a k) s.rollback.accesses.storageKeys` by (
       `toSet s.rollback.accesses.storageKeys ⊆
        toSet s'.rollback.accesses.storageKeys`
          by fs[same_frame_rel_def]
       >> fs[pred_setTheory.SUBSET_DEF, finite_setTheory.fIN_IN]
       >> metis_tac[])
  (* Unfold step = handle inner handle_step. *)
  >> qhdtm_x_assum `step` mp_tac
  >> simp[step_def, handle_def]
  >> qmatch_goalsub_abbrev_tac `pair_CASE (inner s)`
  >> `same_frame_or_grow inner` by simp[Abbr`inner`]
  >> Cases_on `inner s` >> Cases_on `q` >> simp[]
  >- (
    (* inner INL: step returns inner result. *)
    strip_tac >> gvs[]
    (* Unfold inner to get the actual primitives that ran. *)
    >> qhdtm_x_assum `Abbrev` mp_tac
    >> simp[markerTheory.Abbrev_def]
    >> disch_then SUBST_ALL_TAC
    >> qpat_x_assum `_ s = (INL (), r')` mp_tac
    >> simp[bind_def, ignore_bind_def]
    >> simp[get_current_context_def, return_def, fail_def]
    >> Cases_on `s.contexts` >> gvs[]
    >> Cases_on `FLOOKUP (FST h).msgParams.parsed (FST h).pc` >> gvs[]
    >- (
      (* Stop and Invalid cases. *)
      Cases_on `LENGTH (FST h).msgParams.code ≤ (FST h).pc` >> gvs[]
      >> strip_tac
      >> drule step_inst_preserves_non_accessed_storage
      >> simp[is_call_def]
      >> disch_then (qspecl_then [`(FST h).msgParams.callee`, `k`] mp_tac)
      >> simp[])
    (* SOME op: step_inst op; inc_pc_or_jump op. *)
    >> strip_tac
    >> gvs[bind_def, ignore_bind_def, AllCaseEqs()]
    >> rename1 `step_inst op s = (INL _, r_mid)`
    >> `r_mid.rollback = r'.rollback`
         by (mp_tac preserves_rollback_inc_pc_or_jump
             >> rewrite_tac[preserves_rollback_def]
             >> disch_then drule
             >> simp[])
    >> `s.contexts ≠ []` by (strip_tac >> fs[])
    >> Cases_on `is_call op`
    >- (
      (* Call/Create family: step_inst returned INL with same frame length
         (since inc_pc_or_jump is same_frame and r' has same length as s).
         This means an abort path ran — no storage written. *)
      `r_mid.contexts ≠ []` by (
         `(SND (step_inst op s)).contexts ≠ []`
            by metis_tac[step_inst_preserves_nonempty_contexts]
         >> rev_full_simp_tac std_ss [])
      >> `LENGTH r_mid.contexts = LENGTH s.contexts` by (
         `LENGTH r'.contexts = LENGTH r_mid.contexts` by (
            `preserves_same_frame (inc_pc_or_jump op)` by simp[]
            >> metis_tac[psf_imp_length_contexts_preserved])
         >> fs[same_frame_rel_def])
      >> drule_all is_call_same_frame_preserves_storage
      >> disch_then (qspecl_then [`(FST h).msgParams.callee`, `k`] mp_tac)
      >> simp[])
    >> drule step_inst_preserves_non_accessed_storage
    >> simp[]
    >> disch_then (qspecl_then [`(FST h).msgParams.callee`, `k`] mp_tac)
    >> simp[])
  >> strip_tac >>
  qhdtm_x_assum`same_frame_or_grow`mp_tac >>
  simp[same_frame_or_grow_def] >> disch_then drule >> simp[] >>
  strip_tac >- (
    qpat_x_assum`inner _ = _`mp_tac >>
    simp[Abbr`inner`, bind_def,AllCaseEqs()] >>
    simp[get_current_context_def, return_def, option_CASE_rator, COND_RATOR,
         AllCaseEqs()] >>
    rpt strip_tac
    >~ [`step_inst Stop`] >- (
      drule step_inst_preserves_non_accessed_storage >>
      simp[is_call_def] >>
      disch_then(qspecl_then[`a`,`k`]mp_tac) >>
      impl_keep_tac >- (
        gvs[step_inst_def, bind_def, ignore_bind_def,
            set_return_data_def, finish_def, AllCaseEqs(),
            get_current_context_def,set_current_context_def,
            return_def,fail_def] ) >>
      disch_then $ assume_tac o SYM >> gvs[] >>
      irule handle_step_preserves_storage_same_length >>
      drule same_frame_rel_contexts_ne >> simp[] >> strip_tac >>
      conj_asm1_tac >- (
        gvs[same_frame_rel_def] >>
        gvs[outputTo_consistent_def] ) >>
      reverse conj_tac >- goal_assum drule >>
      fs[same_frame_rel_def] )
    >~ [`step_inst Invalid`] >- (
      drule step_inst_preserves_non_accessed_storage >>
      simp[is_call_def] >>
      disch_then(qspecl_then[`a`,`k`]mp_tac) >>
      impl_keep_tac >- (
        gvs[step_inst_def, bind_def, ignore_bind_def,
            set_return_data_def, finish_def, AllCaseEqs(),
            get_current_context_def,set_current_context_def,
            return_def,fail_def] ) >>
      disch_then $ assume_tac o SYM >> gvs[] >>
      irule handle_step_preserves_storage_same_length >>
      drule same_frame_rel_contexts_ne >> simp[] >> strip_tac >>
      conj_asm1_tac >- (
        gvs[same_frame_rel_def] >>
        gvs[outputTo_consistent_def] ) >>
      reverse conj_tac >- goal_assum drule >>
      fs[same_frame_rel_def] ) >>
    pop_assum mp_tac >>
    simp[ignore_bind_def,bind_def] >>
    TOP_CASE_TAC >> strip_tac >>
    reverse (Cases_on `q`) >> gvs[] >- (
      (* step_inst op s = (INR y, r' = r'') *)
      Cases_on `is_call op` >- (
        (* call op INR same-length: use preserves_storage_step_call/create *)
        `lookup_storage k
            (lookup_account (FST (HD s.contexts)).msgParams.callee
               r'.rollback.accounts).storage =
         lookup_storage k
            (lookup_account (FST (HD s.contexts)).msgParams.callee
               s.rollback.accounts).storage` by (
          Cases_on `op` >> fs[is_call_def, step_inst_def]
          >~ [`step_create F s = _`]
          >- (drule step_create_storage >> simp[] >> metis_tac[])
          >~ [`step_create T s = _`]
          >- (drule step_create_storage >> simp[] >> metis_tac[])
          >> metis_tac[preserves_storage_step_call, preserves_storage_def])
        >> irule EQ_TRANS
        >> qexists `lookup_storage k
                      (lookup_account (FST (HD s.contexts)).msgParams.callee
                         r'.rollback.accounts).storage`
        >> reverse conj_tac >- metis_tac[]
        >> irule handle_step_preserves_storage_same_length
        >> drule same_frame_rel_contexts_ne >> simp[] >> strip_tac
        >> conj_asm1_tac >- (gvs[same_frame_rel_def] >> gvs[outputTo_consistent_def])
        >> reverse conj_tac >- goal_assum drule
        >> fs[same_frame_rel_def])
      >> (* non-call op *)
         `outputTo_consistent r'` by (
           fs[outputTo_consistent_def]
           >> `r'.contexts ≠ []` by metis_tac[same_frame_rel_contexts_ne]
           >> `(FST (HD r'.contexts)).msgParams = (FST (HD s.contexts)).msgParams`
                by fs[same_frame_rel_def]
           >> simp[])
         >> `LENGTH s'.contexts = LENGTH r'.contexts` by fs[same_frame_rel_def]
         >> `toSet r'.rollback.accesses.storageKeys SUBSET
                toSet s'.rollback.accesses.storageKeys`
             by metis_tac[handle_step_same_length_storageKeys_subset]
         >> drule step_inst_preserves_non_accessed_storage >> simp[]
         >> disch_then (qspecl_then [`(FST (HD s.contexts)).msgParams.callee`, `k`] mp_tac)
         >> impl_keep_tac
         >- (`toSet r'.rollback.accesses.storageKeys ⊆
              toSet s'.rollback.accesses.storageKeys`
               by fs[same_frame_rel_def]
             >> fs[pred_setTheory.SUBSET_DEF, finite_setTheory.fIN_IN]
             >> metis_tac[])
         >> strip_tac
         >> pop_assum $ assume_tac o SYM >> gvs[]
         >> irule handle_step_preserves_storage_same_length
         >> drule same_frame_rel_contexts_ne >> simp[] >> strip_tac
         >> goal_assum drule)
    >> (* INR from inc_pc_or_jump: use step_inst storage preservation, then
          rollback preservation of inc_pc_or_jump. *)
       Cases_on `is_call op`
       >- ((* is_call op + step_inst INL + inc_pc_or_jump INR: impossible.
              For is_call op, inc_pc_or_jump op = return () which always
              returns (INL (), r). So INR is impossible. *)
           fs[inc_pc_or_jump_def, return_def])
       >> (* non-call op case *)
          `outputTo_consistent r'` by (
            fs[outputTo_consistent_def]
            >> `r'.contexts ≠ []` by metis_tac[same_frame_rel_contexts_ne]
            >> `(FST (HD r'.contexts)).msgParams = (FST (HD s.contexts)).msgParams`
                 by fs[same_frame_rel_def]
            >> simp[])
          >> `LENGTH s'.contexts = LENGTH r'.contexts` by fs[same_frame_rel_def]
          >> `toSet r'.rollback.accesses.storageKeys SUBSET
                toSet s'.rollback.accesses.storageKeys`
             by metis_tac[handle_step_same_length_storageKeys_subset]
          >> `lookup_storage k
                (lookup_account (FST (HD s.contexts)).msgParams.callee
                   r'.rollback.accounts).storage =
              lookup_storage k
                (lookup_account (FST (HD s.contexts)).msgParams.callee
                   s.rollback.accounts).storage` by (
             (* Chain: s → r'' (step_inst) → r' (inc_pc_or_jump).
                inc_pc_or_jump preserves_rollback, so r'.rollback = r''.rollback.
                step_inst_preserves_non_accessed_storage gives storage r'' = storage s
                at non-accessed slots. *)
             qhdtm_x_assum `step_inst` assume_tac
             >> drule step_inst_preserves_non_accessed_storage
             >> simp[]
             >> disch_then (qspecl_then
                 [`(FST (HD s.contexts)).msgParams.callee`, `k`] mp_tac)
             >> `r'.rollback = r''.rollback` by (
                mp_tac preserves_rollback_inc_pc_or_jump
                >> rewrite_tac[preserves_rollback_def]
                >> disch_then drule >> simp[])
             >> fs[]
             >> impl_tac
             >- (`toSet r''.rollback.accesses.storageKeys ⊆
                  toSet s'.rollback.accesses.storageKeys`
                    by (`r''.rollback = r'.rollback` by simp[]
                        >> fs[same_frame_rel_def])
                 >> fs[pred_setTheory.SUBSET_DEF, finite_setTheory.fIN_IN]
                 >> metis_tac[])
             >> strip_tac >> fs[])
          >> pop_assum $ assume_tac o SYM >> gvs[]
          >> irule handle_step_preserves_storage_same_length
          >> simp[]
          >> reverse conj_tac >- goal_assum drule
          >> imp_res_tac same_frame_rel_contexts_ne) >>
  `LENGTH s'.contexts = LENGTH s.contexts` by gvs[same_frame_rel_def] >>
  gvs[Abbr`inner`,bind_def,AllCaseEqs(),get_current_context_def,return_def] >>
  gvs[option_CASE_rator,COND_RATOR,AllCaseEqs()]
  >~ [`step_inst Stop`] >- (
    `¬is_call Stop` by simp[is_call_def] >>
    drule preserves_same_frame_step_inst_not_call >>
    rewrite_tac[preserves_same_frame_def] >>
    disch_then drule >> simp[] >>
    simp[same_frame_rel_def] )
  >~ [`step_inst Invalid`] >- (
    `¬is_call Invalid` by simp[is_call_def] >>
    drule preserves_same_frame_step_inst_not_call >>
    rewrite_tac[preserves_same_frame_def] >>
    disch_then drule >> simp[] >>
    simp[same_frame_rel_def] ) >>
  qpat_x_assum`_ = (INR _, _)`mp_tac >>
  simp[ignore_bind_def,bind_def] >> TOP_CASE_TAC >>
  reverse $ Cases_on`is_call op` >- (
    drule preserves_same_frame_step_inst_not_call >>
    rewrite_tac[preserves_same_frame_def] >>
    disch_then drule >> simp[] >>
    simp[same_frame_rel_def] >> strip_tac >>
    CASE_TAC >> rw[] >> gvs[] >>
    mp_tac preserves_same_frame_inc_pc_or_jump >>
    rewrite_tac[preserves_same_frame_def] >>
    disch_then drule >> simp[] >>
    rw[same_frame_rel_def] >> gvs[] ) >>
  simp[inc_pc_or_jump_def, return_def] >>
  TOP_CASE_TAC >> rw[] >>
  drule_at Any handle_step_pop_generic_gen >>
  Cases_on`r'.contexts`
  >- (qpat_x_assum `LENGTH [] >= _` mp_tac >> simp[]) >>
  gvs[ExclSF "ARITH"] >>
  Cases_on`h` >> gvs[ExclSF "ARITH"] >>
  Cases_on`t`
  >- (qpat_x_assum `SUC (LENGTH []) >= _` mp_tac >>
      Cases_on `s.contexts`
      >- (qpat_x_assum `[] <> []` mp_tac >> simp[]) >> simp[]) >>
  gvs[ExclSF "ARITH"] >>
  (impl_tac >- (qpat_x_assum `SUC _ >= _` mp_tac >> simp[])) >>
  disch_then assume_tac >>
  irule EQ_TRANS >>
  qmatch_goalsub_abbrev_tac`lookup_storage k (lookup_account a _).storage` >>
  qexists_tac`lookup_storage k (lookup_account a r'.rollback.accounts).storage` >>
  reverse conj_tac >- (
    qpat_x_assum`_ ∧ _`kall_tac >>
    Cases_on `op` >> gvs[is_call_def, step_inst_def]
    >~ [`step_create F s = _`]
    >- (drule_all step_create_inr_no_grow >> simp[])
    >~ [`step_create T s = _`]
    >- (drule_all step_create_inr_no_grow >> simp[])
    >> metis_tac[preserves_storage_step_call, preserves_storage_def] ) >>
  (* Relate s'.rollback storage to r'.rollback storage after handle_step. *)
  qpat_x_assum `_ ∧ _` strip_assume_tac
  (* Split the handle_step_pop_generic_gen disjunction. *)
  >- ((* Disjunct A: ∀a. storage s'.rollback @ a = storage r'.rollback @ a. *)
      simp[] >> metis_tac[])
  (* Disjunct B: chain through the pushed rollback storage. *)
  >> `(lookup_account a r''.accounts).storage =
      (lookup_account a s.rollback.accounts).storage` by (
       `LENGTH r'.contexts > LENGTH s.contexts` by simp[]
       >> `SND (HD r'.contexts) = r''` by simp[]
       >> qpat_x_assum `is_call op` mp_tac
       >> Cases_on `op` >> simp[is_call_def]
       >> qpat_x_assum `step_inst _ _ = _`
            (assume_tac o REWRITE_RULE[step_inst_def])
       >> metis_tac[step_call_pushed_rb_storage,
                    step_create_pushed_rb_storage])
  >> `lookup_storage k (lookup_account a s.rollback.accounts).storage =
      lookup_storage k (lookup_account a r'.rollback.accounts).storage` by (
       Cases_on `op` >> full_simp_tac (srw_ss()) [is_call_def, step_inst_def]
       >~ [`step_create F s = _`]
       >- (drule_all step_create_inr_no_grow >> simp[])
       >~ [`step_create T s = _`]
       >- (drule_all step_create_inr_no_grow >> simp[])
       >> metis_tac[preserves_storage_step_call, preserves_storage_def])
  >> `lookup_storage k (lookup_account a s'.rollback.accounts).storage =
      lookup_storage k (lookup_account a r''.accounts).storage` by simp[]
  >> simp[]
QED

Theorem step_preserves_non_accessed_storage:
  ∀s r s'. step s = (r, s') ∧ s.contexts ≠ [] ∧
    outputTo_consistent s ∧
    same_frame_rel s s' ⇒
  ∀a k. ¬fIN (SK a k) s'.rollback.accesses.storageKeys ⇒
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  rpt gen_tac >> strip_tac
  >> `LENGTH s'.contexts = LENGTH s.contexts` by gvs[same_frame_rel_def]
  >> metis_tac[step_same_length_preserves_non_accessed_storage]
QED

(* -------------------------------------------------------------------------
 * Stack room for CALL/CREATE growth.
 * ------------------------------------------------------------------------- *)

Theorem step_call_grow_parent_stack_room:
  wf_context (FST (HD s.contexts)) ∧ step_call op s = (r, s') ∧
  s.contexts ≠ [] ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
    LENGTH (FST (HD (TL s'.contexts))).stack < stack_limit
Proof
  simp[step_call_def] >> strip_tac
  >> qmatch_asmsub_abbrev_tac `pop_stack n`
  >> `0 < n` by (simp[Abbr`n`] >> Cases_on `call_has_value op` >> simp[])
  >> qpat_x_assum `_ s = _` mp_tac
  >> simp[Abbr`n`]
  >> qmatch_goalsub_abbrev_tac `bind (pop_stack n) k s`
  >> Cases_on `pop_stack n s` >> Cases_on `q` >> gvs[bind_def]
  >- (
    rename1 `pop_stack n s = (INL args, sp)`
    >> `LENGTH (FST (HD sp.contexts)).stack < stack_limit ∧
        LENGTH sp.contexts = LENGTH s.contexts` by (
         qpat_x_assum `pop_stack n s = _` mp_tac
         >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
              bind_def, return_def, assert_def, fail_def, set_current_context_def,
              wf_context_def, ignore_bind_def, AllCaseEqs()]
         >> strip_tac >> gvs[])
    >> simp[Abbr`k`]
    >> strip_tac
    >> pairarg_tac >> gvs[]
    (* Peel memory_expansion_info *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ sp = (_,_)`kall_tac
    >> impl_keep_tac >- (strip_tac >> gvs[])
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sp s2`
    >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH sp.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s2.contexts)).stack < stack_limit` by gvs[]
    (* Peel consume_gas *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s2 s3`
    >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s2.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s3.contexts)).stack < stack_limit` by gvs[]
    (* Peel expand_memory *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s3 s4`
    >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s3.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s4.contexts)).stack < stack_limit` by gvs[]
    (* Peel access/read prefix pieces, following step_call_push_structure. *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> impl_keep_tac >- (CASE_TAC >> simp[] >> irule preserves_head_stack_bind
                         >> simp[])
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s4 s5`
    >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s4.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s5.contexts)).stack < stack_limit` by gvs[]
    >> pairarg_tac >> gvs[ignore_bind_def]
    (* EIP-8037: the opcode's execution gas, before the creation charge. *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s5 s6`
    >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s5.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s6.contexts)).stack < stack_limit` by gvs[]
    (* EIP-8037: the account-creation charge, before the child's grant. *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[charge_new_account_def] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s6 sc`
    >> `sc.contexts ≠ [] ∧ LENGTH sc.contexts = LENGTH s6.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sc.contexts)).stack < stack_limit` by gvs[]
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sc s7`
    >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH sc.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s7.contexts)).stack < stack_limit` by gvs[]
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s7 s8`
    >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s7.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s8.contexts)).stack < stack_limit` by gvs[]
    (* The grant is computed after the charge, so the 63/64 rule sees the
       execution gas a spill thinned. *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s8 s9`
    >> `s9.contexts ≠ [] ∧ LENGTH s9.contexts = LENGTH s8.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s9.contexts)).stack < stack_limit` by gvs[]
    >> pairarg_tac >> gvs[ignore_bind_def]
    (* EIP-8037: the child's grant, charged in execution gas too. *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s9 sd`
    >> `sd.contexts ≠ [] ∧ LENGTH sd.contexts = LENGTH s9.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sd.contexts)).stack < stack_limit` by gvs[]
    (* Peel get_callee *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sd s0`
    >> `s0.contexts ≠ [] ∧ LENGTH s0.contexts = LENGTH sd.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s0.contexts)).stack < stack_limit` by gvs[]
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
    >> gvs[Ntimes COND_RATOR 2]
    >> Cases_on`bbb` >> gs[]
    >- (
      drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved
      >> simp[])
    (* Peel set_return_data via ignore_bind *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s0 sa`
    >> `sa.contexts ≠ [] ∧ LENGTH sa.contexts = LENGTH s0.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sa.contexts)).stack < stack_limit` by gvs[]
    (* Peel get_num_contexts *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sa sb`
    >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH sa.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sb.contexts)).stack < stack_limit` by gvs[]
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
    >> gvs[COND_RATOR]
    >> Cases_on`bbb` >> gs[]
    >- (
      drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved
      >> simp[])
    >> drule_all proceed_call_push_structure
    >> strip_tac
    >> gvs[])
  >> (
    (* If pop_stack failed, the state did not grow. *)
    qpat_x_assum `pop_stack n s = _` mp_tac
    >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
         bind_def, return_def, assert_def, fail_def, set_current_context_def]
    >> rw[] >> pop_assum mp_tac
    >> simp[ignore_bind_def,bind_def,assert_def,set_current_context_def,
            return_def,fail_def,AllCaseEqs()] >> rw[]
    >> gvs[Abbr`k`] )
QED

Theorem step_create_grow_parent_stack_room:
  wf_context (FST (HD s.contexts)) ∧ step_create two s = (r, s') ∧
  s.contexts ≠ [] ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
    LENGTH (FST (HD (TL s'.contexts))).stack < stack_limit
Proof
  simp[step_create_def] >> strip_tac
  >> qmatch_asmsub_abbrev_tac `pop_stack n`
  >> `0 < n` by (simp[Abbr`n`] >> Cases_on `two` >> simp[])
  >> qpat_x_assum `_ s = _` mp_tac
  >> simp[Abbr`n`]
  >> qmatch_goalsub_abbrev_tac `bind (pop_stack n) k s`
  >> Cases_on `pop_stack n s` >> Cases_on `q` >> gvs[bind_def]
  >- (
    rename1 `pop_stack n s = (INL args, sp)`
    >> `LENGTH (FST (HD sp.contexts)).stack < stack_limit ∧
        LENGTH sp.contexts = LENGTH s.contexts` by (
         qpat_x_assum `pop_stack n s = _` mp_tac
         >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
              bind_def, return_def, assert_def, fail_def, set_current_context_def,
              wf_context_def, ignore_bind_def, AllCaseEqs()]
         >> strip_tac >> gvs[])
    >> simp[Abbr`k`]
    (* Peel memory_expansion_info *)
    >> strip_tac
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ sp = (_,_)`kall_tac
    >> impl_keep_tac >- (strip_tac >> gvs[])
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sp s2`
    >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH sp.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s2.contexts)).stack < stack_limit` by gvs[]
    (* Peel consume_gas *)
    >> gvs[ignore_bind_def]
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s2 s3`
    >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s2.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s3.contexts)).stack < stack_limit` by gvs[]
    (* Peel expand_memory *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s3 s4`
    >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s3.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s4.contexts)).stack < stack_limit` by gvs[]
    (* Peel read_memory *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s4 s5`
    >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s4.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s5.contexts)).stack < stack_limit` by gvs[]
    (* Peel get_callee *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s5 s6`
    >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s5.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s6.contexts)).stack < stack_limit` by gvs[]
    (* Peel get_accounts *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s6 s7`
    >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH s6.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s7.contexts)).stack < stack_limit` by gvs[]
    (* Peel assert (code length) via ignore_bind *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s7 s8`
    >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s7.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD s8.contexts)).stack < stack_limit` by gvs[]
    (* Peel assert_not_static *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s8 sb`
    >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH s8.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sb.contexts)).stack < stack_limit` by gvs[]
    (* Peel set_return_data *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sb sc`
    >> `sc.contexts ≠ [] ∧ LENGTH sc.contexts = LENGTH sb.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sc.contexts)).stack < stack_limit` by gvs[]
    (* Peel get_num_contexts *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sc sd`
    >> `sd.contexts ≠ [] ∧ LENGTH sd.contexts = LENGTH sc.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sd.contexts)).stack < stack_limit` by gvs[]
    (* Split the preliminary failure condition. *)
    >> qmatch_asmsub_abbrev_tac`COND preliminaryFailure _ _ _ = (_, _)`
    >> gvs[COND_RATOR]
    >> qpat_x_assum`COND preliminaryFailure _ _ = _`mp_tac
    >> IF_CASES_TAC
    >- (strip_tac >> drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved >> simp[])
    >> strip_tac
    (* Peel access_address *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sd sx`
    >> `sx.contexts ≠ [] ∧ LENGTH sx.contexts = LENGTH sd.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sx.contexts)).stack < stack_limit` by gvs[]
    (* Peel ensure_storage_in_domain *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sx sy`
    >> `sy.contexts ≠ [] ∧ LENGTH sy.contexts = LENGTH sx.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sy.contexts)).stack < stack_limit` by gvs[]
    (* EIP-8037: the destination's creation, charged before the child's
       grant is withheld so a spill thins what is withheld. *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[charge_new_account_def] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sy sz`
    >> `sz.contexts ≠ [] ∧ LENGTH sz.contexts = LENGTH sy.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD sz.contexts)).stack < stack_limit` by gvs[]
    (* Peel withhold_create_gas *)
    >> drule_at (Pat`bind`) bind_psf_phs_grows_extract
    >> simp[preserves_same_frame_state_gas_meter] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sz se`
    >> `se.contexts ≠ [] ∧ LENGTH se.contexts = LENGTH sz.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `LENGTH (FST (HD se.contexts)).stack < stack_limit` by gvs[]
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
    >> gvs[COND_RATOR]
    >> qpat_x_assum`COND bbb _ _ = _`mp_tac
    >> IF_CASES_TAC
    >- (strip_tac >> drule (REWRITE_RULE[length_preserves_def] length_preserves_abort_create_exists) >> simp[])
    >> strip_tac
    >> drule_all proceed_create_push_structure
    >> strip_tac
    >> gvs[])
  >> (
    qpat_x_assum `pop_stack n s = _` mp_tac
    >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
         bind_def, return_def, assert_def, fail_def, set_current_context_def]
    >> rw[] >> pop_assum mp_tac
    >> simp[ignore_bind_def, bind_def, assert_def, set_current_context_def,
            return_def, fail_def, AllCaseEqs()] >> rw[]
    >> gvs[Abbr`k`] )
QED

Theorem step_call_grow_parent_gas_monotone:
  step_call op s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
    (FST (HD s.contexts)).gasUsed ≤ (FST (EL 1 s'.contexts)).gasUsed
Proof
  simp[step_call_def] >> strip_tac
  >> qmatch_asmsub_abbrev_tac `pop_stack n`
  >> qpat_x_assum `_ s = _` mp_tac
  >> simp[Abbr`n`]
  >> qmatch_goalsub_abbrev_tac `bind (pop_stack n) k s`
  >> Cases_on `pop_stack n s` >> Cases_on `q` >> gvs[bind_def]
  >- (
    rename1 `pop_stack n s = (INL args, sp)`
    >> `s.contexts ≠ [] ∧ sp.contexts ≠ [] ∧
        (FST (HD s.contexts)).gasUsed ≤ (FST (HD sp.contexts)).gasUsed ∧
        LENGTH sp.contexts = LENGTH s.contexts` by (
         qpat_x_assum `pop_stack n s = _` mp_tac
         >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
              bind_def, return_def, assert_def, fail_def, set_current_context_def,
              ignore_bind_def, AllCaseEqs()]
         >> strip_tac >> gvs[])
    >> simp[Abbr`k`]
    >> strip_tac
    >> pairarg_tac >> gvs[]
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ sp = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sp s2`
    >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH sp.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s2.contexts)).gasUsed` by decide_tac
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s2 s3`
    >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s2.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s3.contexts)).gasUsed` by decide_tac
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s3 s4`
    >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s3.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s4.contexts)).gasUsed` by decide_tac
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> impl_keep_tac >- (CASE_TAC >> simp[] >> irule preserves_head_gas_mono_bind >> simp[])
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s4 s5`
    >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s4.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s5.contexts)).gasUsed` by decide_tac
    >> pairarg_tac >> gvs[ignore_bind_def]
    (* EIP-8037: the opcode's own execution gas, the creation charge in state
       gas, the static check and the memory expansion all come before the
       child's grant is read. *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s5 s6`
    >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s5.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s6.contexts)).gasUsed` by decide_tac
    (* EIP-8037: the recipient's creation, charged in state gas before the
       child's grant is computed so a spill thins what the 63/64 rule sees. *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s6 s7`
    >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH s6.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s7.contexts)).gasUsed` by decide_tac
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s7 s8`
    >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s7.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s8.contexts)).gasUsed` by decide_tac
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s8 s9`
    >> `s9.contexts ≠ [] ∧ LENGTH s9.contexts = LENGTH s8.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s9.contexts)).gasUsed` by decide_tac
    (* The grant is computed after the charge, so the 63/64 rule sees the
       execution gas a spill thinned. *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> pairarg_tac >> gvs[ignore_bind_def]
    >> rename1`same_frame_rel s9 sc`
    >> `sc.contexts ≠ [] ∧ LENGTH sc.contexts = LENGTH s9.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sc.contexts)).gasUsed` by decide_tac
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sc sd`
    >> `sd.contexts ≠ [] ∧ LENGTH sd.contexts = LENGTH sc.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sd.contexts)).gasUsed` by decide_tac
    (* Peel get_callee *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sd s0`
    >> `s0.contexts ≠ [] ∧ LENGTH s0.contexts = LENGTH sd.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s0.contexts)).gasUsed` by decide_tac
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
    >> gvs[Ntimes COND_RATOR 2]
    >> Cases_on`bbb` >> gs[]
    >- (drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved >> simp[])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s0 sa`
    >> `sa.contexts ≠ [] ∧ LENGTH sa.contexts = LENGTH s0.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sa.contexts)).gasUsed` by decide_tac
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sa sb`
    >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH sa.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sb.contexts)).gasUsed` by decide_tac
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
    >> gvs[COND_RATOR]
    >> Cases_on`bbb` >> gs[]
    >- (drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved >> simp[])
    >> drule_all proceed_call_push_structure
    >> strip_tac
    >> `EL 1 s'.contexts = HD (TL s'.contexts)` by
         (Cases_on `s'.contexts` >> gvs[EL_CONS])
    >> simp[] )
  >> (
    qpat_x_assum `pop_stack n s = _` mp_tac
    >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
         bind_def, return_def, assert_def, fail_def, set_current_context_def]
    >> rw[] >> pop_assum mp_tac
    >> simp[ignore_bind_def, bind_def, assert_def, set_current_context_def,
            return_def, fail_def, AllCaseEqs()] >> rw[]
    >> gvs[Abbr`k`] )
QED

Theorem step_create_grow_parent_gas_monotone:
  step_create two s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
    (FST (HD s.contexts)).gasUsed ≤ (FST (EL 1 s'.contexts)).gasUsed
Proof
  simp[step_create_def] >> strip_tac
  >> qmatch_asmsub_abbrev_tac `pop_stack n`
  >> qpat_x_assum `_ s = _` mp_tac
  >> simp[Abbr`n`]
  >> qmatch_goalsub_abbrev_tac `bind (pop_stack n) k s`
  >> Cases_on `pop_stack n s` >> Cases_on `q` >> gvs[bind_def]
  >- (
    rename1 `pop_stack n s = (INL args, sp)`
    >> `s.contexts ≠ [] ∧ sp.contexts ≠ [] ∧
        (FST (HD s.contexts)).gasUsed ≤ (FST (HD sp.contexts)).gasUsed ∧
        LENGTH sp.contexts = LENGTH s.contexts` by (
         qpat_x_assum `pop_stack n s = _` mp_tac
         >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
              bind_def, return_def, assert_def, fail_def, set_current_context_def,
              ignore_bind_def, AllCaseEqs()]
         >> strip_tac >> gvs[])
    >> simp[Abbr`k`]
    >> strip_tac
    (* memory_expansion_info *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ sp = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sp s2`
    >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH sp.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s2.contexts)).gasUsed` by decide_tac
    (* consume_gas *)
    >> gvs[ignore_bind_def]
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s2 s3`
    >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s2.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s3.contexts)).gasUsed` by decide_tac
    (* expand_memory *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s3 s4`
    >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s3.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s4.contexts)).gasUsed` by decide_tac
    (* read_memory *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s4 s5`
    >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s4.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s5.contexts)).gasUsed` by decide_tac
    (* get_callee *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s5 s6`
    >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s5.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s6.contexts)).gasUsed` by decide_tac
    (* get_accounts *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s6 s7`
    >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH s6.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s7.contexts)).gasUsed` by decide_tac
    (* assert code length *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s7 s8`
    >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s7.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD s8.contexts)).gasUsed` by decide_tac
    (* assert_not_static *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s8 sa`
    >> `sa.contexts ≠ [] ∧ LENGTH sa.contexts = LENGTH s8.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sa.contexts)).gasUsed` by decide_tac
    (* set_return_data *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sa sb`
    >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH sa.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sb.contexts)).gasUsed` by decide_tac
    (* get_num_contexts *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sb sd`
    >> `sd.contexts ≠ [] ∧ LENGTH sd.contexts = LENGTH sb.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sd.contexts)).gasUsed` by decide_tac
    (* Split the preliminary failure condition. *)
    >> qmatch_asmsub_abbrev_tac`COND preliminaryFailure _ _ _ = (_, _)`
    >> gvs[COND_RATOR]
    >> qpat_x_assum`COND preliminaryFailure _ _ = _`mp_tac
    >> IF_CASES_TAC
    >- (strip_tac >> drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved >> simp[])
    >> strip_tac
    (* access_address *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sd sx`
    >> `sx.contexts ≠ [] ∧ LENGTH sx.contexts = LENGTH sd.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sx.contexts)).gasUsed` by decide_tac
    (* ensure_storage_in_domain *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sx sy`
    >> `sy.contexts ≠ [] ∧ LENGTH sy.contexts = LENGTH sx.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sy.contexts)).gasUsed` by decide_tac
    (* EIP-8037: the destination's creation, charged in state gas before the
       child's grant is withheld so a spill thins what is withheld. *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sy sz`
    >> `sz.contexts ≠ [] ∧ LENGTH sz.contexts = LENGTH sy.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD sz.contexts)).gasUsed` by decide_tac
    (* EIP-8037: the child's grant is withheld after the charge, so the
       63/64 rule sees the gas a spill thinned. *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[]
    >> (impl_tac >- (simp[withhold_create_gas_def] >>
         irule preserves_head_gas_mono_bind >> simp[] >> gen_tac >>
         irule preserves_head_gas_mono_ignore_bind >> simp[]))
    >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sz se`
    >> `se.contexts ≠ [] ∧ LENGTH se.contexts = LENGTH sz.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> `(FST (HD s.contexts)).gasUsed ≤ (FST (HD se.contexts)).gasUsed` by decide_tac
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
    >> gvs[COND_RATOR]
    >> qpat_x_assum`COND bbb _ _ = _`mp_tac
    >> IF_CASES_TAC
    >- (strip_tac >> drule (REWRITE_RULE[length_preserves_def] length_preserves_abort_create_exists) >> simp[])
    >> strip_tac
    >> drule_all proceed_create_push_structure
    >> strip_tac
    >> `EL 1 s'.contexts = HD (TL s'.contexts)` by
         (Cases_on `s'.contexts` >> gvs[EL_CONS])
    >> simp[])
  >> (
    qpat_x_assum `pop_stack n s = _` mp_tac
    >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
         bind_def, return_def, assert_def, fail_def, set_current_context_def]
    >> rw[] >> pop_assum mp_tac
    >> simp[ignore_bind_def, bind_def, assert_def, set_current_context_def,
            return_def, fail_def, AllCaseEqs()] >> rw[]
    >> gvs[Abbr`k`] )
QED

Theorem call_gas_stipend_le_consumed:
  (if 0 < value then call_stipend else 0) ≤ otherCost + memoryCost ∧
  call_gas value gas gasLeft memoryCost otherCost = (dynamicGas, stipend) ⇒
  stipend ≤ dynamicGas + memoryCost
Proof
  rw[call_gas_def]
QED

Theorem proceed_call_parent_gas_ok:
  proceed_call op sender address value argsOffset argsSize code stipend outputTo s = (r, s') ∧
  s.contexts ≠ [] ∧
  oldGas + stipend ≤ (FST (HD s.contexts)).gasUsed ⇒
    oldGas +
    ((FST (HD s'.contexts)).msgParams.gasLimit -
     (FST (HD s'.contexts)).gasUsed) ≤
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  strip_tac
  >> qhdtm_x_assum `proceed_call` mp_tac
  >> simp[proceed_call_def, drain_state_gas_reservoir_def,
          bind_def, ignore_bind_def, get_current_context_def,
          set_current_context_def, return_def, get_accounts_def]
  >> simp[bind_def, get_rollback_def, return_def]
  >> simp[read_memory_def, bind_def, return_def, get_current_context_def]
  >> qmatch_goalsub_abbrev_tac `COND transfer _ _`
  >> Cases_on `transfer`
  >> qpat_x_assum `Abbrev _` kall_tac
  >> (simp[update_accounts_def, return_def]
  >> qmatch_goalsub_abbrev_tac `get_caller s1`
  >> `s1.contexts <> [] /\
      (FST (HD s1.contexts)).gasUsed = (FST (HD s.contexts)).gasUsed`
       by simp[Abbr `s1`]
  >> rewrite_tac[Once bind_def]
  >> simp[get_caller_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_value_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_static_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_static_def, return_def, get_current_context_def]
  >> rewrite_tac[Once bind_def]
  >> TOP_CASE_TAC
  >> drule push_context_effect >> strip_tac >> gvs[]
  >> qmatch_asmsub_abbrev_tac `push_context (ctx, _) s1`
  >> reverse IF_CASES_TAC
  >- (
    rw[return_def]
    >> gvs[Abbr`ctx`, initial_context_def, initial_msg_params_def])
  >> strip_tac
  >> qmatch_asmsub_abbrev_tac `dispatch_precompiles addr ss = (_, s')`
  >> `ss.contexts ≠ []` by simp[Abbr`ss`]
  >> qmatch_asmsub_abbrev_tac `dpa ss = (_,_)`
  >> `preserves_same_frame dpa` by simp[Abbr`dpa`]
  >> pop_assum mp_tac
  >> rewrite_tac[preserves_same_frame_def]
  >> disch_then drule
  >> simp[same_frame_rel_def]
  >> strip_tac
  >> gvs[Abbr`ctx`, Abbr`ss`, initial_context_def, initial_msg_params_def]
  >> Cases_on`s'.contexts` >> gvs[])
QED

Theorem proceed_create_parent_gas_ok:
  proceed_create senderAddress address value code cappedGas s = (r, s') ∧
  s.contexts ≠ [] ∧
  oldGas + cappedGas ≤ (FST (HD s.contexts)).gasUsed ⇒
    oldGas +
    ((FST (HD s'.contexts)).msgParams.gasLimit -
     (FST (HD s'.contexts)).gasUsed) ≤
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  strip_tac
  >> qhdtm_x_assum `proceed_create` mp_tac
  >> simp[proceed_create_def, drain_state_gas_reservoir_def,
          get_current_context_def, set_current_context_def,
          bind_def, ignore_bind_def, return_def, get_accounts_def]
  >> simp[ignore_bind_def, Once bind_def, update_accounts_def, return_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_rollback_def, return_def]
  >> rewrite_tac[Once bind_def]
  >> simp[get_original_def, return_def, fail_def]
  >> rewrite_tac[Once bind_def]
  >> simp[set_original_def, return_def, fail_def]
  >> rewrite_tac[Once bind_def]
  >> simp[update_accounts_def, return_def]
  >> strip_tac
  >> drule push_context_effect >> strip_tac
  >> gvs[initial_context_def, initial_msg_params_def]
  >> qspec_then`s.contexts`FULL_STRUCT_CASES_TAC SNOC_CASES >> gvs[]
  >> gvs[set_last_accounts_def,update_account_def]
  >> Cases_on`l` >> gvs[]
QED

Theorem proceed_call_parent_unused_gas_ok:
  proceed_call op sender address value argsOffset argsSize code stipend outputTo s = (r,s') /\
  s.contexts <> [] /\ oldGas + stipend <= (FST (HD s.contexts)).gasUsed ==>
  oldGas + frame_unused_gas (FST (HD s'.contexts)) <=
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  strip_tac >> Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
  qhdtm_x_assum `proceed_call` mp_tac >>
  simp[proceed_call_def, drain_state_gas_reservoir_def,
       bind_def, ignore_bind_def, get_current_context_def,
       set_current_context_def, return_def, get_rollback_def,
       read_memory_def, get_caller_def, get_value_def, get_static_def,
       get_accounts_def] >>
  Cases_on `op <> CallCode /\ 0 < value` >>
  (simp[update_accounts_def, return_def, push_context_def, bind_def] >>
   qmatch_goalsub_abbrev_tac `(if _ then _ else _) ss` >>
   Cases_on `fIN address precompile_addresses`
   >- (simp[] >> strip_tac >>
       qspec_then `address` mp_tac
         (GEN_ALL (INST_TYPE [alpha |-> ``:unit``] decreases_gas_dispatch_precompiles)) >>
       rewrite_tac[decreases_gas_def] >>
       disch_then (qspec_then `ss` mp_tac) >>
       qhdtm_x_assum `dispatch_precompiles`
         (fn th => pure_rewrite_tac[th]) >>
       simp[Abbr `ss`] >> strip_tac >>
       gvs[initial_context_def, initial_msg_params_def, frame_unused_gas_def]) >>
   simp[return_def, Abbr `ss`, initial_context_def, initial_msg_params_def,
        frame_unused_gas_def] >> strip_tac >> gvs[])
QED

Theorem proceed_create_parent_unused_gas_ok:
  proceed_create senderAddress address value code cappedGas s = (r,s') /\
  s.contexts <> [] /\ oldGas + cappedGas <= (FST (HD s.contexts)).gasUsed ==>
  oldGas + frame_unused_gas (FST (HD s'.contexts)) <=
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  strip_tac >> qhdtm_x_assum `proceed_create` mp_tac >>
  simp[proceed_create_def, drain_state_gas_reservoir_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, update_accounts_def,
       get_rollback_def, get_original_def, set_original_def,
       get_accounts_def] >>
  strip_tac >> drule push_context_effect >> strip_tac >>
  gvs[initial_context_def, initial_msg_params_def, frame_unused_gas_def] >>
  qspec_then `s.contexts` FULL_STRUCT_CASES_TAC SNOC_CASES >> gvs[] >>
  gvs[set_last_accounts_def, update_account_def] >> Cases_on `l` >> gvs[]
QED

Theorem step_call_grow_parent_weight_ok:
  (!op sender address value argsOffset argsSize code stipend outputTo t r u b.
    proceed_call op sender address value argsOffset argsSize code stipend outputTo t = (r,u) /\
    t.contexts <> [] /\ b + stipend <= (FST (HD t.contexts)).gasUsed ==>
    b + weight (FST (HD u.contexts)) <= (FST (EL 1 u.contexts)).gasUsed) ==>
  wf_state s ∧ step_call op s = (r, s') ∧
  is_call op ∧ (op ≠ Create ∧ op ≠ Create2) ∧
  s.contexts ≠ [] ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
    (FST (HD s.contexts)).gasUsed + weight (FST (HD s'.contexts)) ≤
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  disch_then (mk_asm "coverage") >> simp[step_call_def] >> strip_tac
  >> qmatch_asmsub_abbrev_tac `pop_stack n`
  >> qpat_x_assum `_ s = _` mp_tac
  >> simp[Abbr`n`]
  >> qmatch_goalsub_abbrev_tac `bind (pop_stack n) k s`
  >> Cases_on `pop_stack n s` >> Cases_on `q` >> gvs[bind_def]
  >- (
    rename1 `pop_stack n s = (INL args, sp)`
    >> `s.contexts ≠ [] ∧ sp.contexts ≠ [] ∧
        (FST (HD s.contexts)).gasUsed = (FST (HD sp.contexts)).gasUsed ∧
        LENGTH sp.contexts = LENGTH s.contexts` by (
         qpat_x_assum `pop_stack n s = _` mp_tac
         >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
              bind_def, return_def, assert_def, fail_def, set_current_context_def,
              ignore_bind_def, AllCaseEqs()]
         >> strip_tac >> gvs[])
    >> simp[Abbr`k`]
    >> strip_tac
    >> pairarg_tac >> gvs[]
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ sp = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sp s2`
    >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH sp.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> simp[] >> strip_tac
    >> rename1`same_frame_rel s2 s3`
    >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s2.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s3 s4`
    >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s3.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> impl_keep_tac
    >- (CASE_TAC >> simp[] >> irule preserves_head_gas_mono_bind >> simp[])
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s4 s5`
    >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s4.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* EIP-8037: the opcode's own execution gas is charged before the
       recipient's creation, so the grant the 63/64 rule applies to is what
       is left of it. *)
    >> pairarg_tac >> gvs[ignore_bind_def]
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s5 s6`
    >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s5.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> qmatch_asmsub_abbrev_tac `consume_gas execCost s5 = _`
    >> `((FST (HD s.contexts)).gasUsed + execCost ≤
          (FST (HD s6.contexts)).gasUsed)` by (
       qhdtm_x_assum`consume_gas`mp_tac >>
       simp[consume_gas_def, bind_def,get_current_context_def,return_def] >>
       simp[assert_def,ignore_bind_def,bind_def,CaseEq"bool",CaseEq"sum"] >>
       simp[set_current_context_def,return_def] >> strip_tac >>
       gvs[] )
    (* EIP-8037: the recipient's creation, in state gas, before the grant. *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s6 sc`
    >> `sc.contexts ≠ [] ∧ LENGTH sc.contexts = LENGTH s6.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sc s7`
    >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH sc.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s7 s8`
    >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s7.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* The grant is computed after the charge, so the 63/64 rule sees the
       execution gas a spill thinned. *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> pairarg_tac >> gvs[]
    >> rename1`same_frame_rel s8 s9`
    >> `s9.contexts ≠ [] ∧ LENGTH s9.contexts = LENGTH s8.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> gvs[ignore_bind_def]
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[]
    >> qpat_x_assum`_ _ = (_,stipend)`(markerLib.ASSUME_NAMED_TAC"cg")
    >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s9 sd`
    >> `sd.contexts ≠ [] ∧ LENGTH sd.contexts = LENGTH s9.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> qmatch_asmsub_abbrev_tac `consume_gas grantCost s9 = _`
    >> `((FST (HD s9.contexts)).gasUsed + grantCost ≤
          (FST (HD sd.contexts)).gasUsed)` by (
       qhdtm_x_assum`consume_gas`mp_tac >>
       simp[consume_gas_def, bind_def,get_current_context_def,return_def] >>
       simp[assert_def,ignore_bind_def,bind_def,CaseEq"bool",CaseEq"sum"] >>
       simp[set_current_context_def,return_def] >> strip_tac >>
       gvs[] )
    (* EIP-8037: the two execution charges are additive, so what the prefix
       spends is the opcode's own cost plus the child's grant. *)
    >> `((FST (HD s.contexts)).gasUsed + (execCost + grantCost) ≤
          (FST (HD sd.contexts)).gasUsed)` by decide_tac
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sd s0`
    >> `s0.contexts ≠ [] ∧ LENGTH s0.contexts = LENGTH sd.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
    >> gvs[Ntimes COND_RATOR 2]
    >> Cases_on`bbb` >> gs[]
    >- (drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved >> simp[])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s0 sa`
    >> `sa.contexts ≠ [] ∧ LENGTH sa.contexts = LENGTH s0.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sa sb`
    >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH sa.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
    >> gvs[COND_RATOR]
    >> Cases_on`bbb` >> gs[]
    >- (drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved >> simp[])
    >> asm "coverage" drule
    >> disch_then (irule o ONCE_REWRITE_RULE [ADD_COMM])
    >> simp[]
    >> qmatch_goalsub_abbrev_tac`stipend + spg <= sbg`
    >> qpat_x_assum`_ + spg <= _`mp_tac
    >> qmatch_goalsub_abbrev_tac`_ <= s7g`
    >> `s7g <= sbg` by simp[]
    (* EIP-8037: the parent spends its own execution gas and then the whole
       grant, and the stipend the child carries is the value transfer's own
       cost, already inside that execution gas. *)
    >> `s7g + callGas <= sbg` by decide_tac
    >> `stipend <= execCost + callGas` suffices_by decide_tac
    >> qunabbrev_tac`execCost`
    >> markerLib.LABEL_ASSUM"cg"assume_tac
    >> qhdtm_x_assum`call_gas`mp_tac
    >> simp[call_gas_def, call_stipend_def, call_value_cost_def]
    >> strip_tac
    >> qpat_x_assum`_ = stipend`(fn th => SUBST_ALL_TAC (SYM th))
    >> Cases_on`0 < (if 0 < if call_has_value op then 1 else 0
                       then w2n (EL 2 args) else 0)`
    >> gvs[] >> decide_tac )
  >> (
    qpat_x_assum `pop_stack n s = _` mp_tac
    >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
         bind_def, return_def, assert_def, fail_def, set_current_context_def]
    >> rw[] >> pop_assum mp_tac
    >> simp[ignore_bind_def, bind_def, assert_def, set_current_context_def,
            return_def, fail_def, AllCaseEqs()] >> rw[]
    >> gvs[Abbr`k`] )
QED

Theorem step_call_grow_parent_gas_ok:
  wf_state s ∧ step_call op s = (r, s') ∧
  is_call op ∧ (op ≠ Create ∧ op ≠ Create2) ∧
  s.contexts ≠ [] ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
    (FST (HD s.contexts)).gasUsed +
    ((FST (HD s'.contexts)).msgParams.gasLimit -
     (FST (HD s'.contexts)).gasUsed) ≤
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  strip_tac >>
  irule (BETA_RULE (Q.INST [`weight` |-> `\c. c.msgParams.gasLimit - c.gasUsed`]
    step_call_grow_parent_weight_ok)) >>
  metis_tac[proceed_call_parent_gas_ok]
QED

Theorem step_create_grow_parent_weight_ok:
  (!senderAddress address value code cappedGas t r u b.
    proceed_create senderAddress address value code cappedGas t = (r,u) /\
    t.contexts <> [] /\ b + cappedGas <= (FST (HD t.contexts)).gasUsed ==>
    b + weight (FST (HD u.contexts)) <= (FST (EL 1 u.contexts)).gasUsed) ==>
  wf_state s ∧ step_create two s = (r, s') ∧
  s.contexts ≠ [] ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
    (FST (HD s.contexts)).gasUsed + weight (FST (HD s'.contexts)) ≤
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  disch_then (mk_asm "coverage") >> simp[step_create_def] >> strip_tac
  >> qmatch_asmsub_abbrev_tac `pop_stack n`
  >> qpat_x_assum `_ s = _` mp_tac
  >> simp[Abbr`n`]
  >> qmatch_goalsub_abbrev_tac `bind (pop_stack n) k s`
  >> Cases_on `pop_stack n s` >> Cases_on `q` >> gvs[bind_def]
  >- (
    rename1 `pop_stack n s = (INL args, sp)`
    >> `s.contexts ≠ [] ∧ sp.contexts ≠ [] ∧
        (FST (HD s.contexts)).gasUsed ≤ (FST (HD sp.contexts)).gasUsed ∧
        LENGTH sp.contexts = LENGTH s.contexts` by (
         qpat_x_assum `pop_stack n s = _` mp_tac
         >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
              bind_def, return_def, assert_def, fail_def, set_current_context_def,
              ignore_bind_def, AllCaseEqs()]
         >> strip_tac >> gvs[])
    >> simp[Abbr`k`]
    >> strip_tac
    (* Same peel as gas monotonicity, with additive cappedGas reservation. *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ sp = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sp s2`
    >> `s2.contexts ≠ [] ∧ LENGTH s2.contexts = LENGTH sp.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> gvs[ignore_bind_def]
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s2 s3`
    >> `s3.contexts ≠ [] ∧ LENGTH s3.contexts = LENGTH s2.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s3 s4`
    >> `s4.contexts ≠ [] ∧ LENGTH s4.contexts = LENGTH s3.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s4 s5`
    >> `s5.contexts ≠ [] ∧ LENGTH s5.contexts = LENGTH s4.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s5 s6`
    >> `s6.contexts ≠ [] ∧ LENGTH s6.contexts = LENGTH s5.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s6 s7`
    >> `s7.contexts ≠ [] ∧ LENGTH s7.contexts = LENGTH s6.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* assert code length *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s7 s8`
    >> `s8.contexts ≠ [] ∧ LENGTH s8.contexts = LENGTH s7.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* assert_not_static *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel s8 sb`
    >> `sb.contexts ≠ [] ∧ LENGTH sb.contexts = LENGTH s8.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* set_return_data *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sb sc`
    >> `sc.contexts ≠ [] ∧ LENGTH sc.contexts = LENGTH sb.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* get_num_contexts *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sc sd`
    >> `sd.contexts ≠ [] ∧ LENGTH sd.contexts = LENGTH sc.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* Split the preliminary failure condition. *)
    >> qmatch_asmsub_abbrev_tac`COND preliminaryFailure _ _ _ = (_, _)`
    >> gvs[COND_RATOR]
    >> qpat_x_assum`COND preliminaryFailure _ _ = _`mp_tac
    >> IF_CASES_TAC
    >- (strip_tac >> drule_at (Pat`_ = (_, s')`) psf_imp_length_contexts_preserved >> simp[])
    >> strip_tac
    (* access_address *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sd sx`
    >> `sx.contexts ≠ [] ∧ LENGTH sx.contexts = LENGTH sd.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* ensure_storage_in_domain *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sx sy`
    >> `sy.contexts ≠ [] ∧ LENGTH sy.contexts = LENGTH sx.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* EIP-8037: the destination's creation, charged before the child's
       grant is withheld so a spill thins what is withheld. *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[] >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sy sz`
    >> `sz.contexts ≠ [] ∧ LENGTH sz.contexts = LENGTH sy.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    (* withhold_create_gas: the additive execution-gas reservation. *)
    >> drule_at (Pat`bind`) bind_psf_phgm_grows_extract
    >> simp[]
    >> (impl_tac >- (simp[withhold_create_gas_def] >>
         irule preserves_head_gas_mono_bind >> simp[] >> gen_tac >>
         irule preserves_head_gas_mono_ignore_bind >> simp[]))
    >> qpat_x_assum`_ _ = (_,_)`kall_tac
    >> strip_tac >> gvs[]
    >> rename1`same_frame_rel sz se`
    >> `se.contexts <> [] /\ LENGTH se.contexts = LENGTH sz.contexts`
         by (rpt strip_tac >> gvs[same_frame_rel_def])
    >> qpat_x_assum `withhold_create_gas sz = (INL _, se)` mp_tac
    >> simp[withhold_create_gas_def, get_gas_left_def,
            get_current_context_def, bind_def, ignore_bind_def, return_def]
    >> strip_tac >> gvs[AllCaseEqs()]
    >> rename1 `consume_gas cappedGas sz = _`
    >> `(FST (HD sz.contexts)).gasUsed + cappedGas <=
        (FST (HD se.contexts)).gasUsed` by
         (drule consume_gas_head_gas_add_ge >> simp[])
    >> qmatch_asmsub_abbrev_tac`COND bbb _ _ _ = (_, _)`
    >> gvs[COND_RATOR]
    >> qpat_x_assum`COND bbb _ _ = _`mp_tac
    >> IF_CASES_TAC
    >- (strip_tac >> drule (REWRITE_RULE[length_preserves_def] length_preserves_abort_create_exists) >> simp[])
    >> strip_tac
    >> asm "coverage" (irule o ONCE_REWRITE_RULE [ADD_COMM])
    >> goal_assum $ drule_at Any
    >> simp[]
    (* EIP-8037: the grant is withheld only after the destination's creation
       is charged, so both come out of the same execution gas. *)
    >> decide_tac)
  >> (
    qpat_x_assum `pop_stack n s = _` mp_tac
    >> Cases_on `s.contexts` >> gvs[pop_stack_def, get_current_context_def,
         bind_def, return_def, assert_def, fail_def, set_current_context_def]
    >> rw[] >> pop_assum mp_tac
    >> simp[ignore_bind_def, bind_def, assert_def, set_current_context_def,
            return_def, fail_def, AllCaseEqs()] >> rw[]
    >> gvs[Abbr`k`] )
QED

Theorem step_create_grow_parent_gas_ok:
  wf_state s ∧ step_create two s = (r, s') ∧
  s.contexts ≠ [] ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
    (FST (HD s.contexts)).gasUsed +
    ((FST (HD s'.contexts)).msgParams.gasLimit -
     (FST (HD s'.contexts)).gasUsed) ≤
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  strip_tac >>
  irule (BETA_RULE (Q.INST [`weight` |-> `\c. c.msgParams.gasLimit - c.gasUsed`]
    step_create_grow_parent_weight_ok)) >>
  metis_tac[proceed_create_parent_gas_ok]
QED

Theorem step_call_grow_parent_unused_gas_ok:
  wf_state s /\ step_call op s = (r,s') /\
  is_call op /\ (op <> Create /\ op <> Create2) /\
  s.contexts <> [] /\ LENGTH s'.contexts > LENGTH s.contexts ==>
  (FST (HD s.contexts)).gasUsed + frame_unused_gas (FST (HD s'.contexts)) <=
  (FST (EL 1 s'.contexts)).gasUsed
Proof
  strip_tac >>
  irule (Q.INST [`weight` |-> `frame_unused_gas`] step_call_grow_parent_weight_ok) >>
  metis_tac[proceed_call_parent_unused_gas_ok]
QED

Theorem step_create_grow_parent_unused_gas_ok:
  wf_state s /\ step_create two s = (r,s') /\
  s.contexts <> [] /\ LENGTH s'.contexts > LENGTH s.contexts ==>
  (FST (HD s.contexts)).gasUsed + frame_unused_gas (FST (HD s'.contexts)) <=
  (FST (EL 1 s'.contexts)).gasUsed
Proof
  strip_tac >>
  irule (Q.INST [`weight` |-> `frame_unused_gas`] step_create_grow_parent_weight_ok) >>
  metis_tac[proceed_create_parent_unused_gas_ok]
QED

Theorem step_inner_grow_parent_unused_gas_ok:
  step_inner s = (r,s') /\ wf_state s /\ s.contexts <> [] /\
  LENGTH s'.contexts > LENGTH s.contexts ==>
  frame_unused_gas (FST (HD s'.contexts)) <= (FST (EL 1 s'.contexts)).gasUsed
Proof
  strip_tac >>
  gvs[step_inner_def, bind_def, get_current_context_def, COND_RATOR,
      fail_def, return_def, CaseEq "bool", CaseEq "prod",
      option_CASE_rator, CaseEq "option", ignore_bind_def]
  >- (`preserves_same_frame (step_inst Stop)` by simp[] >>
      drule_all psf_imp_length_contexts_preserved >> simp[])
  >- (`preserves_same_frame (step_inst Invalid)` by simp[] >>
      drule_all psf_imp_length_contexts_preserved >> simp[]) >>
  gvs[CaseEq "sum", CaseEq "prod"]
  >- (mp_tac preserves_same_frame_inc_pc_or_jump >>
      rewrite_tac[preserves_same_frame_def] >>
      disch_then drule >> simp[] >>
      (impl_tac >- metis_tac[step_inst_preserves_nonempty_contexts, SND]) >>
      strip_tac >>
      `is_call op` by
        (drule step_inst_inl_grew_is_call >> gvs[same_frame_rel_def]) >>
      gvs[inc_pc_or_jump_def, return_def] >>
      Cases_on `op = Create \/ op = Create2`
      >- (gvs[step_inst_def] >>
          drule_all step_create_grow_parent_unused_gas_ok >> decide_tac) >>
      `step_inst op s = step_call op s` by
        (Cases_on `op` >> gvs[step_inst_def, is_call_def]) >>
      gvs[] >> drule_all step_call_grow_parent_unused_gas_ok >> decide_tac) >>
  drule step_inst_inr_grew_is_call_family >> simp[] >> strip_tac >>
  `step_inst op s = step_call op s` by gvs[step_inst_def] >>
  gvs[] >>
  drule_at (Pat `step_call`) step_call_grow_parent_unused_gas_ok >>
  simp[is_call_def] >> decide_tac
QED

Theorem step_grow_parent_unused_gas_ok:
  step s = (r,s') /\ wf_state s /\ s.contexts <> [] /\
  outputTo_consistent_stack s /\ LENGTH s'.contexts > LENGTH s.contexts ==>
  frame_unused_gas (FST (HD s'.contexts)) <= (FST (EL 1 s'.contexts)).gasUsed
Proof
  strip_tac >> qhdtm_x_assum `step` mp_tac >>
  simp[step_eq_handle_step_inner, handle_def] >>
  Cases_on `step_inner s` >> Cases_on `q`
  >- (simp[] >> strip_tac >> gvs[] >>
      drule_all step_inner_grow_parent_unused_gas_ok >> simp[]) >>
  simp[] >> strip_tac >> rename1 `handle_step e sm = (_,s')` >>
  `same_frame_or_grow step_inner` by simp[] >>
  `LENGTH sm.contexts >= LENGTH s.contexts` by
    (drule_all same_frame_or_grow_length >> simp[]) >>
  `sm.contexts <> []` by (strip_tac >> gvs[] >> Cases_on `s.contexts` >> gvs[]) >>
  Cases_on `LENGTH sm.contexts = LENGTH s.contexts`
  >- (drule handle_step_shrinks_by_one >> simp[]) >>
  `LENGTH sm.contexts > LENGTH s.contexts` by simp[] >>
  `outputTo_consistent s` by metis_tac[outputTo_consistent_stack_imp_consistent] >>
  `~vfm_abort e` by
    (irule step_inner_inr_grow_not_abort >>
     qpat_x_assum `step_inner s = _` mp_tac >> simp[step_inner_def] >>
     strip_tac >> goal_assum $ drule_at Any >> simp[]) >>
  `LENGTH sm.contexts = LENGTH s.contexts + 1` by
    (qpat_x_assum `step_inner s = _` mp_tac >> simp[step_inner_def] >>
     strip_tac >> drule_then drule step_inner_grows_by_exactly_one >> simp[]) >>
  `LENGTH sm.contexts >= 2` by (Cases_on `s.contexts` >> gvs[]) >>
  drule_at (Pat `handle_step`) handle_step_not_abort_pops >> simp[] >>
  `EVERY (wf_context o FST) sm.contexts` suffices_by
    (rpt (pop_assum kall_tac) >> rw[EVERY_MEM, EXISTS_MEM, o_DEF] >> metis_tac[]) >>
  mp_tac decreases_gas_cred_step_inner >> gvs[decreases_gas_cred_def] >>
  disch_then (qspec_then `s` mp_tac) >> rw[] >> gvs[wf_state_def]
QED

(* Named facts about the pre-handler inner step. *)

(* Full-step push structure: storage/access shape plus parent stack/gas facts. *)
Theorem step_push_structure:
  ∀s r s'. step s = (r, s') ∧ s.contexts ≠ [] ∧
    outputTo_consistent_stack s ∧ wf_state s ∧
    LENGTH s'.contexts > LENGTH s.contexts ⇒
    LENGTH s'.contexts = LENGTH s.contexts + 1 ∧
    (* Storage preservation for s'.rollback, except that CREATE clears the
       storage of the address it creates *)
    (∀a. (lookup_account a s'.rollback.accounts).storage =
         (lookup_account a s.rollback.accounts).storage ∨
         (lookup_account a s'.rollback.accounts).storage = empty_storage ∧
         ¬account_already_created (lookup_account a s.rollback.accounts)) ∧
    toSet s.rollback.accesses.storageKeys ⊆
      toSet s'.rollback.accesses.storageKeys ∧
    (* saved rollback storage; CREATE's old-LAST exception is excluded *)
    (∀i. i < LENGTH s.contexts ⇒
         (∀a. (lookup_account a (SND (EL i s'.contexts)).accounts).storage =
              (lookup_account a (if i = 0 then s.rollback
                                 else SND (EL (i-1) s.contexts)).accounts).storage)) ∧
    (∀i. i < LENGTH s'.contexts ⇒
         toSet (if i = 0 then s.rollback
                else SND (EL (i-1) s.contexts)).accesses.storageKeys ⊆
           toSet (SND (EL i s'.contexts)).accesses.storageKeys) ∧
    (* saved parent / shifted tail *)
    MAP FST (TL (TL s'.contexts)) = MAP FST (TL s.contexts) ∧
    LENGTH (FST (EL 1 s'.contexts)).stack < stack_limit ∧
    (FST (EL 1 s'.contexts)).gasUsed ≥ (FST (HD s.contexts)).gasUsed ∧
    (FST (HD s.contexts)).gasUsed +
      ((FST (HD s'.contexts)).msgParams.gasLimit -
       (FST (HD s'.contexts)).gasUsed) ≤
      (FST (EL 1 s'.contexts)).gasUsed ∧
    (* parent msgParams *)
    (LENGTH s.contexts ≥ 1 ⇒
       (FST (EL 1 s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams) ∧
    (* new child outputTo consistency *)
    outputTo_consistent_ctx (FST (HD s'.contexts)) ∧
    (* shifted outputTo consistency *)
    (∀i. i < LENGTH s.contexts ⇒
         outputTo_consistent_ctx (FST (EL i s.contexts)) ⇒
         outputTo_consistent_ctx (FST (EL (i+1) s'.contexts)))
Proof
  rpt gen_tac >> strip_tac
  (* Unfold step = handle inner handle_step *)
  >> qpat_x_assum `step s = _` mp_tac
  >> simp[step_def, handle_def]
  >> qmatch_goalsub_abbrev_tac `inner s`
  >> Cases_on `inner s` >> Cases_on `q`
  (* Case: inner returned INL - step returns inner's result *)
  >- (
    simp[] >> strip_tac >> gvs[]
    (* inner = get_ctx; step_inst; inc_pc_or_jump *)
    >> gvs[Abbr`inner`, bind_def,AllCaseEqs()]
    >> gvs[get_current_context_def, return_def, fail_def, bind_def]
    >> gvs[option_CASE_rator,CaseEq"option"]
    >> gvs[COND_RATOR, CaseEq"bool"]
    (* Case: NONE, code ≤ pc, step_inst Stop *)
    >~ [`step_inst Stop`]
    >- (
      `preserves_same_frame (step_inst Stop)` by simp[]
      >> drule_all psf_imp_length_contexts_preserved
      >> simp[])
    (* NONE: step_inst Invalid *)
    >~ [`step_inst Invalid`]
    >- (
      `preserves_same_frame (step_inst Invalid)` by simp[]
      >> drule_all psf_imp_length_contexts_preserved
      >> simp[])
    (* SOME op: step_inst op; inc_pc_or_jump op *)
    >> gvs[ignore_bind_def, bind_def]
    >> gvs[AllCaseEqs()]
    >> rename1 `step_inst op s0 = (INL (), s1)`
    >> drule_at Any psf_imp_length_contexts_preserved
    >> simp[]
    >> impl_keep_tac >- (strip_tac >>
         gvs[inc_pc_or_jump_def,COND_RATOR,AllCaseEqs(),return_def] >>
         gvs[bind_def,get_current_context_def,fail_def,AllCaseEqs()] )
    >> strip_tac
    >> `LENGTH s1.contexts > LENGTH s0.contexts` by simp[]
    (* By step_inst_inl_grew_is_call, is_call op *)
    >> `is_call op` by metis_tac[step_inst_inl_grew_is_call]
    (* For is_call, inc_pc_or_jump = return (), so s' = s1 *)
    >> `r' = s1` by (
         gvs[inc_pc_or_jump_def, return_def, COND_RATOR, CaseEq"bool"])
    >> gvs[]
    >> `outputTo_consistent s0` by (
         gvs[outputTo_consistent_def, outputTo_consistent_stack_def]
         >> Cases_on`s0.contexts`
         >> gvs[outputTo_consistent_ctx_def])
    (* Case split on which call/create op *)
    >> Cases_on `∃two. step_inst op s0 = step_create two s0`
    >- (
      (* CREATE/CREATE2 case *)
      gvs[] >> pop_assum(assume_tac o SYM) >>
      (* Use step_create lemmas *)
      drule_then drule step_create_grows_by_exactly_one
      >> simp[] >> strip_tac
      (* CREATE either leaves the storage object alone or clears it. *)
      >> conj_tac
      >- (drule step_create_storage_object >> simp[] >> metis_tac[])
      (* Use step_create_push_structure *)
      >> drule step_create_push_structure
      >> simp[]
      >> strip_tac
      >> drule_then drule step_create_pushed_rb_storage
      >> simp[] >> strip_tac
      >> conj_tac
      >- ( Cases >> simp[] >> Cases_on`r'.contexts` >> gvs[] )
      >> conj_tac >- ( Cases >> gvs[] >> Cases_on`r'.contexts` >> gvs[] )
      >> drule_at Any step_create_grow_parent_stack_room
      >> impl_tac >- ( gvs[wf_state_def] >> Cases_on`s0.contexts` >> gvs[] )
      >> strip_tac
      >> conj_tac >- (
        qmatch_goalsub_rename_tac`EL 1 rr.contexts` >>
        Cases_on`rr.contexts` >> gvs[] )
      >> Cases_on`s0.contexts` >> gvs[]
      >> Cases_on`r'.contexts` >> gvs[]
      >> Cases_on`t'` >> gvs[]
      >> drule step_create_grow_parent_gas_monotone
      >> simp[] >> strip_tac
      >> drule_at(Pat`step_create`) step_create_grow_parent_gas_ok
      >> simp[] >> strip_tac
      >> Cases >> gvs[EL_CONS]
      >- ( simp[outputTo_consistent_ctx_def] )
      >> gvs[PRE_SUB1,ADD1]
      >> simp[outputTo_consistent_ctx_def]
      >> gvs[LIST_EQ_REWRITE,EL_MAP])
    >> (
      (* CALL family case *)
      `step_inst op s0 = step_call op s0`
      by (Cases_on`op` >> gvs[step_inst_def, is_call_def])
      (* Use step_call lemmas *)
      >> gvs[]
      >> drule_then drule step_call_grows_by_exactly_one
      >> simp[] >> strip_tac
      (* s1.rollback storage preserved *)
      >> drule(REWRITE_RULE[preserves_storage_def]preserves_storage_step_call)
      >> simp[lookup_storage_def, FUN_EQ_THM]
      >> strip_tac
      >> drule_all step_call_pushed_rb_storage
      >> strip_tac
      (* Use step_call_push_structure *)
      >> drule_all step_call_push_structure
      >> strip_tac
      >> simp[]
      >> conj_tac
      >- (
        Cases >> gvs[ADD1] >>
        Cases_on`r'.contexts` >> gvs[EL_CONS,PRE_SUB1] >>
        Cases_on`s0.contexts` >> gvs[ADD1] >>
        Cases_on`t` >> gvs[ADD1] >>
        Cases_on`n` >> gvs[ADD1] )
      >> drule_at(Pat`step_call`)step_call_grow_parent_stack_room
      >> impl_tac >- ( gvs[wf_state_def] >> Cases_on`s0.contexts` >- gvs[] >>
                       simp[] >> fs[])
      >> strip_tac
      >> Cases_on`r'.contexts` >> gvs[EL_CONS, PRE_SUB1]
      >> Cases_on`t` >> gvs[EL_CONS, PRE_SUB1, ADD1]
      >> Cases_on`s0.contexts` >> gvs[EL_CONS, PRE_SUB1, ADD1]
      >> drule step_call_grow_parent_gas_monotone
      >> simp[] >> strip_tac
      >> drule_at(Pat`step_call`)step_call_grow_parent_gas_ok
      >> simp[]
      >> impl_tac >- (rpt strip_tac >> gs[step_inst_def])
      >> strip_tac >> gvs[]
      >> conj_tac >> Cases >> gvs[ADD1]
      >- ( Cases_on`n` >> gvs[] )
      >> gvs[outputTo_consistent_ctx_def]))
  (* Case: inner returned INR - handle_step runs *)
  >> simp[]
  >> rename1 `handle_step e r' = (_, s')`
  (* inner is same_frame_or_grow *)
  >> `same_frame_or_grow inner` by simp[Abbr`inner`]
  >> `LENGTH r'.contexts ≥ LENGTH s.contexts` by (
       drule_all same_frame_or_grow_length >> simp[])
  >> strip_tac
  >> `r'.contexts ≠ []` by (strip_tac >> gvs[] >> Cases_on`s.contexts` >> gvs[])
  (* Inner INR-grow cannot lead to full-step growth: non-abort handlers pop;
     aborts reraise and preserve the inner length. *)
  >> `LENGTH s'.contexts ≤ LENGTH s.contexts` suffices_by gvs[]
  >> Cases_on `LENGTH r'.contexts = LENGTH s.contexts` >- (
       drule handle_step_shrinks_by_one >> simp[])
  (* inner grew *)
  >> `LENGTH r'.contexts > LENGTH s.contexts` by simp[]
  >> `outputTo_consistent s` by
       metis_tac[outputTo_consistent_stack_imp_consistent]
  >> `¬vfm_abort e` by (
       irule step_inner_inr_grow_not_abort
       >> qexistsl_tac [`s`, `r'`] >> simp[Abbr`inner`])
  >> `0 < LENGTH s.contexts` by (Cases_on`s.contexts` >> gvs[])
  >> `LENGTH r'.contexts ≥ 2` by simp[]
  (* Inner grew by exactly 1 *)
  >> `LENGTH r'.contexts = LENGTH s.contexts + 1` by (
       qunabbrev_tac`inner` >>
       drule_then drule step_inner_grows_by_exactly_one >> gvs[])
  (* Need EVERY (wf_context o FST) r'.contexts to apply handle_step_not_abort_pops *)
  >> drule_at(Pat`handle_step`) handle_step_not_abort_pops
  >> gvs[]
  >> `decreases_gas_cred T 0 0 inner` suffices_by (
    gvs[decreases_gas_cred_def] >>
    disch_then(qspec_then`s`mp_tac) >> rw[] >>
    gvs[wf_state_def] >>
    gvs[EVERY_MEM] ) >>
  simp[Abbr`inner`] >>
  irule decreases_gas_cred_bind_mono >>
  qexistsl_tac[`T`,`F`] >> simp[] >> gen_tac >>
  rw[] >> CASE_TAC >> rw[] >>
  irule decreases_gas_cred_ignore_bind_mono >> rw[] >>
  qexistsl_tac[`F`,`T`] >> simp[]
QED

(* Reusable pre-handler push structure for step_inner. *)

Theorem step_inner_push_structure:
  wf_state s ∧ step_inner s = (r, s') ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
    LENGTH s'.contexts = LENGTH s.contexts + 1 ∧
    MAP FST (TL (TL s'.contexts)) = MAP FST (TL s.contexts) ∧
    LENGTH (FST (EL 1 s'.contexts)).stack < stack_limit ∧
    (FST (EL 1 s'.contexts)).gasUsed ≥
      (FST (HD s.contexts)).gasUsed ∧
    (FST (HD s.contexts)).gasUsed +
      ((FST (HD s'.contexts)).msgParams.gasLimit -
       (FST (HD s'.contexts)).gasUsed) ≤
      (FST (EL 1 s'.contexts)).gasUsed ∧
    (FST (EL 1 s'.contexts)).msgParams =
      (FST (HD s.contexts)).msgParams
Proof
  strip_tac
  >> Cases_on `r`
  >- (
    `step s = (INL x, s')` by simp[step_eq_handle_step_inner, handle_def]
    >> drule step_push_structure
    >> gvs[wf_state_def]
    >> strip_tac
    >> Cases_on`s.contexts` >> gvs[] )
  (* Inner INR-growth can only be CALL-family. *)
  >> gvs[step_inner_def, bind_def, get_current_context_def, COND_RATOR,
         fail_def,return_def,CaseEq"bool",CaseEq"prod",
         option_CASE_rator,CaseEq"option",ignore_bind_def]
  >> TRY (drule step_inst_inr_grew_is_call_family >> simp[] >> NO_TAC)
  >> mp_tac step_inst_preserves_nonempty_contexts
  >> impl_keep_tac >- (strip_tac >> gvs[wf_state_def])
  >> simp[Excl"step_inst_preserves_nonempty_contexts"] >> strip_tac
  >> gvs[CaseEq"sum",CaseEq"prod"]
  >- (
    drule step_inst_inl_grew_is_call >> simp[] >>
    mp_tac preserves_same_frame_inc_pc_or_jump >>
    rewrite_tac[preserves_same_frame_def] >>
    disch_then drule >> simp[] >>
    ntac 2 strip_tac >> gvs[same_frame_rel_def] >>
    gvs[inc_pc_or_jump_def,return_def] )
  >> drule step_inst_inr_grew_is_call_family
  >> simp[] >> disch_then(markerLib.ASSUME_NAMED_TAC"call")
  >> `step_inst op s = step_call op s`
       by (markerLib.LABEL_ASSUM"call"strip_assume_tac >> gvs[step_inst_def])
  >> gvs[]
  >> drule_then drule step_call_grows_by_exactly_one
  >> simp[] >> strip_tac
  >> drule_all step_call_push_structure
  >> strip_tac
  >> drule_at(Pat`step_call`) step_call_grow_parent_stack_room
  >> Cases_on`s.contexts` >> fs[]
  >> impl_keep_tac >- (gvs[wf_state_def])
  >> strip_tac
  >> drule step_call_grow_parent_gas_monotone
  >> simp[] >> strip_tac
  >> drule_at(Pat`step_call`) step_call_grow_parent_gas_ok
  >> simp[]
  >> impl_tac >- (markerLib.LABEL_ASSUM"call"strip_assume_tac >> simp[is_call_def])
  >> strip_tac
  >> Cases_on `s'.contexts` >> gvs[]
QED

(* Full-step pop structure.  Rollback equality is weakened to storage equality
 * plus the matching accesses subset, because handle_create may change code. *)
(* EIP-8037 replacement for `step_inst_same_frame_gas_monotone`, which was
   false.  `credit_state_gas_refund` (`spec/vfmExecutionScript.sml:518-527`)
   takes `MIN n stateGasSpilled` out of the frame's `gasUsed`, and
   `step_sstore_gas_consumption` runs it before its charges (`:1016`, charges
   at `:1021-1022`), so a slot-clearing SSTORE on a frame that has already
   spilled can end below its starting `gasUsed`.  Checked witness:
   `spec/prop/vfmSstoreGasProbeScript.sml`
   `step_inst_same_frame_gas_monotone_counterexample`.

   The measure is what survives: the credit lowers `gasUsed` and the spill
   together and puts the excess in the reservoir, which `frame_unused_gas`
   does not count, so it leaves the measure alone; `charge_state_gas` moves both
   together on its spill branch; and `update_gas_refund` never touches
   `gasUsed`.  Inside a same-frame step the head's `frame_unused_gas` can
   therefore only fall, by `consume_gas`. *)
Theorem step_inst_same_frame_unused_gas_monotone:
   step_inst op s = (q, s') ∧
   same_frame_rel s s' ∧
   EVERY (wf_context o FST) s.contexts
   ⇒
     frame_unused_gas (FST (HD s'.contexts)) ≤
     frame_unused_gas (FST (HD s.contexts))
Proof
  strip_tac
  >> qspec_then`op`mp_tac(GEN_ALL decreases_gas_cred_step_inst)
  >> rewrite_tac[decreases_gas_cred_def]
  >> disch_then(qspec_then`s`mp_tac)
  >> simp[]
  >> gvs[same_frame_rel_def]
  >> Cases_on`s.contexts` >> gvs[]
  >> Cases_on`s'.contexts` >> gvs[]
  >> gvs[contexts_weight_def, unused_gas_def, LEX_DEF]
  >> strip_tac >> Cases_on `ISL q` >> gvs[]
QED

(* EIP-8037: this used to bound `new_head.gasUsed` by the parent's, less the
   child's leftover execution gas.  That bound is dropped rather than weakened:
   the frame whose meter pays the merge's spill repayment is the head of the
   intermediate state, which `step` does not name, so the repayment
   `MIN stateGasLeft stateGasSpilled` cannot be written in this statement's
   variables, and any existential over it would be satisfied by every value. *)
Theorem step_pop_structure:
  ∀s r s'. step s = (r, s') ∧ s.contexts ≠ [] ∧
    outputTo_consistent_stack s ∧
    EVERY (wf_context o FST) s.contexts ∧
    LENGTH s'.contexts < LENGTH s.contexts ⇒
    ∃new_head parent rest.
      s.contexts = HD s.contexts :: parent :: rest ∧
      s'.contexts = (new_head, SND parent) :: rest ∧
      new_head.msgParams = (FST parent).msgParams ∧
      ((toSet s.rollback.accesses.storageKeys ⊆
          toSet s'.rollback.accesses.storageKeys ∧
        (∀a. (lookup_account a s'.rollback.accounts).storage =
             (lookup_account a s.rollback.accounts).storage)) ∨
       (toSet (SND (HD s.contexts)).accesses.storageKeys ⊆
          toSet s'.rollback.accesses.storageKeys ∧
        (∀a. (lookup_account a s'.rollback.accounts).storage =
             (lookup_account a (SND (HD s.contexts)).accounts).storage)))
Proof
  rpt strip_tac
  >> qpat_x_assum `step s = (r,s')` mp_tac
  >> simp[step_def, handle_def]
  >> qmatch_goalsub_abbrev_tac `inner s`
  >> Cases_on `inner s` >> Cases_on `q` >> gvs[Abbr `inner`]
  >- (rpt strip_tac >> assume_tac same_frame_or_grow_step_inner
      >> drule_all same_frame_or_grow_length >> fs[])
  >> rpt strip_tac
  >> ASSUME_TAC same_frame_or_grow_step_inner
  >> `LENGTH r'.contexts >= LENGTH s.contexts`
       by (drule_all same_frame_or_grow_length >> fs[])
  >> `r'.contexts <> []` by (Cases_on `r'.contexts` >> fs[])
  >> `LENGTH s'.contexts + 1 >= LENGTH r'.contexts /\
      LENGTH s'.contexts <= LENGTH r'.contexts`
       by (drule handle_step_shrinks_by_one >> fs[])
  >> `LENGTH r'.contexts = LENGTH s.contexts` by decide_tac
  >> `same_frame_rel s r'` by (drule_all same_frame_or_grow_eq_length >> fs[])
  >> `LENGTH s.contexts >= 2` by (
       CCONTR_TAC >> fs[]
       >> `LENGTH s.contexts <= 1` by decide_tac
       >> `LENGTH s.contexts = 1` by decide_tac
       >> drule handle_step_preserves_length_1 >> fs[])
  >> `s.contexts = HD s.contexts :: TL s.contexts`
       by (Cases_on `s.contexts` >> fs[])
  >> `LENGTH (TL s.contexts) >= 1`
       by (Cases_on `TL s.contexts` >> fs[])
  >> `?parent rest. TL s.contexts = parent :: rest`
       by (Cases_on `TL s.contexts` >> fs[])
  >> `r'.contexts <> []` by fs[same_frame_rel_def]
  >> `TL r'.contexts = TL s.contexts /\ SND (HD r'.contexts) = SND (HD s.contexts)`
       by fs[same_frame_rel_def]
  >> `r'.contexts = (FST (HD r'.contexts), SND (HD s.contexts)) :: parent :: rest`
       by (Cases_on `r'.contexts` >> fs[] >> Cases_on `h` >> fs[])
  >> `LENGTH s'.contexts < LENGTH r'.contexts` by decide_tac
  (* Use paired lemma. Split its disjunction into two separate subgoals
     via strip_assume_tac, avoiding gvs contamination.
     DISJ1(r'): storage s'.rollback = storage r'.rollback
     DISJ2(r'): storage s'.rollback = storage (SND (HD r'.contexts)) *)
  >> Cases_on`y`
  >- (
    gvs[bind_def,get_current_context_def,return_def,fail_def]
    >> Cases_on`∃op. step_inst op s = (INR NONE, r')`
    >- (
      gvs[] >>
      drule_all step_inst_inr_preserves_storage >> rw[] >>
      drule_at_then(Pat`handle_step`)drule
        handle_step_pop_generic_gen_paired >>
      simp[] >>
      Cases_on`s.contexts` >> gvs[] >>
      Cases_on`r'.contexts` >> gvs[wf_context_def] >>
      Cases_on`s'.contexts` >> gvs[] >>
      disch_then (qx_choosel_then [`new_head`] strip_assume_tac) >>
      gvs[lookup_storage_def, FUN_EQ_THM] >>
      gvs[SUBSET_DEF,same_frame_rel_def] )
    >> gvs[option_CASE_rator, AllCaseEqs()]
    >> gvs[COND_RATOR,AllCaseEqs()]
    >> gvs[ignore_bind_def,bind_def,AllCaseEqs()]
    >> drule inc_pc_or_jump_inr_eq >> rw[] )
  >> gvs[handle_step_def]
  >> gvs[COND_RATOR,CaseEq"bool",reraise_def]
  >> gvs[handle_def,CaseEq"prod"]
  >> gvs[handle_create_reraises_when_some]
  >> gvs[reraise_def]
  >> gvs[bind_def, get_current_context_def, return_def]
  >> reverse(Cases_on`x = Reverted`)
  >- (
    drule_at(Pat`handle_exception`)handle_exception_pop_failure_rollback_gen >>
    simp[] >> Cases_on`r'.contexts` >> gvs[] >>
    Cases_on`h` >> gvs[] >> Cases_on`s'.contexts` >> gvs[] >>
    Cases_on`h` >> gvs[] >> strip_tac >>
    gvs[same_frame_rel_def] >>
    Cases_on`s.contexts` >> fs[] >>
    BasicProvers.VAR_EQ_TAC >> fs[] >>
    drule_at(Pat`handle_exception`)handle_exception_pop_generic_gen >>
    simp[] >> strip_tac >> gvs[]
  )
  >> drule_at(Pat`handle_exception`)handle_exception_pop_generic_gen
  >> simp[]
  >> Cases_on`r'.contexts` >> gvs[]
  >> Cases_on`h` >> gvs[]
  >> rpt strip_tac >> gvs[]
  >- (
    qexists_tac`parent` >> gvs[] >>
    gvs[same_frame_rel_def] >>
    Cases_on`s.contexts` >> fs[] >>
    disj1_tac >> qx_gen_tac`a` >>
    qmatch_asmsub_abbrev_tac`callee_local_changes callee` >>
    reverse(Cases_on`a = callee`) >- (
      gvs[callee_local_changes_def] ) >>
    gvs[bind_def,get_current_context_def,return_def,AllCaseEqs()] >>
    Cases_on`∃op. step_inst op s = (INR (SOME Reverted),r')`
    >- (
      gvs[] >>
      drule step_inst_inr_preserves_storage >>
      simp[lookup_storage_def, FUN_EQ_THM] ) >>
    gvs[option_CASE_rator,AllCaseEqs()] >>
    gvs[COND_RATOR,AllCaseEqs()] >>
    gvs[ignore_bind_def,bind_def,AllCaseEqs()] >>
    drule inc_pc_or_jump_inr_eq >> rw[]) >>
  Cases_on`s.contexts` >> fs[] >>
  gvs[wf_context_def] >>  gvs[same_frame_rel_def]
QED

(* -------------------------------------------------------------------------
 * Full wf_state preservation. Placed here because the strong wf_state
 * invariants use whole-step push/pop structure proved above.
 * ------------------------------------------------------------------------- *)

Theorem step_push_parent_stack_room:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s'.contexts > LENGTH s.contexts
  ⇒ LENGTH (FST (EL 1 s'.contexts)).stack < stack_limit
Proof
  rpt strip_tac
  >> drule step_push_structure
  >> gvs[]
  >> impl_tac >- gvs[wf_state_def]
  >> strip_tac
  >> simp[]
QED

Theorem step_preserves_stack_room_ok:
  wf_state s ⇒ stack_room_ok (SND (step s))
Proof
  strip_tac
  >> Cases_on `step s` >> simp[]
  >> rename1 `step s = (_, s')`
  >> rename1 `step s = (r, s')`
  >> Cases_on `LENGTH s'.contexts = LENGTH s.contexts`
  >- (
    `outputTo_consistent s`
      by metis_tac[wf_state_def, outputTo_consistent_stack_imp_consistent] >>
    `same_frame_rel (zero_head_refunds s) s'` by
      metis_tac[step_same_frame, zero_head_refunds_def] >>
    irule same_frame_rel_preserves_stack_room_ok >>
    qexists_tac `zero_head_refunds s` >> simp[] >>
    gvs[wf_state_def, stack_room_ok_def, zero_head_refunds_def] >>
    Cases_on `s.contexts` >> gvs[])
  >> Cases_on `LENGTH s'.contexts > LENGTH s.contexts`
  >- (
    `LENGTH (FST (EL 1 s'.contexts)).stack < stack_limit`
      by metis_tac[step_push_parent_stack_room] >>
    drule step_push_structure >> impl_tac >- gvs[wf_state_def] >>
    strip_tac >>
    gvs[stack_room_ok_def, wf_state_def] >>
    Cases_on `s'.contexts` >> gvs[] >>
    Cases_on `t` >> gvs[] >>
    rw[EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
    gvs[])
  >> (
    `LENGTH s'.contexts < LENGTH s.contexts` by decide_tac >>
    `outputTo_consistent_stack s` by gvs[wf_state_def] >>
    drule step_pop_structure >> simp[] >>
    impl_tac >- (rpt strip_tac >> gvs[wf_state_def]) >>
    strip_tac >>
    gvs[stack_room_ok_def, wf_state_def] >>
    Cases_on`s.contexts` >> gvs[]
  )
QED

Theorem same_frame_rel_preserves_outputTo_consistent_stack:
  same_frame_rel s s' ∧ outputTo_consistent_stack s ⇒
  outputTo_consistent_stack s'
Proof
  rw[outputTo_consistent_stack_def, same_frame_rel_def]
  >> Cases_on `s.contexts` >> gvs[]
  >> Cases_on `s'.contexts` >> gvs[]
  >> gvs[outputTo_consistent_ctx_def]
QED

Theorem step_preserves_outputTo_consistent_stack:
  wf_state s ⇒ outputTo_consistent_stack (SND (step s))
Proof
  strip_tac
  >> Cases_on `step s` >> simp[]
  >> rename1 `step s = (_, s')`
  >> rename1 `step s = (r, s')`
  >> Cases_on `LENGTH s'.contexts = LENGTH s.contexts`
  >- (
    `outputTo_consistent s`
    by metis_tac[wf_state_def, outputTo_consistent_stack_imp_consistent] >>
    `same_frame_rel (zero_head_refunds s) s'` by
      metis_tac[step_same_frame, zero_head_refunds_def] >>
    irule same_frame_rel_preserves_outputTo_consistent_stack >>
    qexists_tac `zero_head_refunds s` >> simp[] >>
    gvs[wf_state_def, outputTo_consistent_stack_def, zero_head_refunds_def] >>
    Cases_on `s.contexts` >> gvs[outputTo_consistent_ctx_def])
  >> Cases_on `LENGTH s'.contexts > LENGTH s.contexts`
  >- (
    drule step_push_structure >> impl_tac >- gvs[wf_state_def] >>
    strip_tac >>
    gvs[outputTo_consistent_stack_def, EVERY_MEM, MEM_EL] >>
    conj_tac >- (strip_tac >> gvs[]) >>
    rw[] >>
    Cases_on `n` >> gvs[] >- (
      Cases_on`s'.contexts` >> gvs[] ) >>
    simp[ADD1, EL_MAP] >> gvs[ADD1] >>
    first_x_assum irule >>
    gvs[wf_state_def,outputTo_consistent_stack_def] >>
    gvs[EVERY_EL, EL_MAP] ) >>
  `LENGTH s'.contexts < LENGTH s.contexts` by decide_tac >>
  `outputTo_consistent_stack s` by gvs[wf_state_def] >>
  gvs[wf_state_def] >>
  drule_all step_pop_structure >>
  Cases_on `s.contexts` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on`s'.contexts` >> gvs[] >>
  strip_tac >> gvs[outputTo_consistent_stack_def] >>
  gvs[outputTo_consistent_ctx_def]
QED

Theorem step_push_parent_gas_ok:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
    (FST (HD s.contexts)).gasUsed +
    ((FST (HD s'.contexts)).msgParams.gasLimit -
     (FST (HD s'.contexts)).gasUsed) ≤
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  rpt strip_tac
  >> drule step_push_structure
  >> simp[]
  >> impl_tac >- gvs[wf_state_def]
  >> strip_tac >> simp[]
QED

(* The `step_inner` counterpart of `step_inst_same_frame_unused_gas_monotone`
   above, replacing `step_inner_same_frame_gas_monotone` for the same reason:
   `step_inner` is `step_inst` of the decoded op plus `inc_pc_or_jump`
   (`vfmExecutionPropScript.sml:40-52`), so the SSTORE credit reaches it too. *)
Theorem step_inner_same_frame_unused_gas_monotone:
  step_inner s = (r, s') ∧ same_frame_rel s s' ∧
  EVERY (wf_context o FST) s.contexts ⇒
    frame_unused_gas (FST (HD s'.contexts)) ≤
    frame_unused_gas (FST (HD s.contexts))
Proof
  rpt strip_tac
  >> mp_tac decreases_gas_cred_step_inner
  >> rewrite_tac[decreases_gas_cred_def]
  >> disch_then(qspec_then `s` mp_tac)
  >> IF_CASES_TAC >> gvs[same_frame_rel_def]
  >> strip_tac
  >> Cases_on `s.contexts` >> gvs[]
  >> Cases_on `s'.contexts` >> gvs[]
  >> gvs[contexts_weight_def, unused_gas_def, LEX_DEF]
  >> Cases_on `ISL r` >> gvs[]
QED

Theorem inner_push_preserves_stack_room_ok:
  wf_state s ∧ step_inner s = (r, s') ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
    stack_room_ok s'
Proof
  rpt strip_tac
  >> drule step_inner_push_structure
  >> simp[] >> strip_tac
  >> gvs[stack_room_ok_def, wf_state_def]
  >> Cases_on `s'.contexts` >> gvs[]
  >> Cases_on `t` >> gvs[]
  >> rw[EVERY_MEM, MEM_MAP, PULL_EXISTS]
  >> gvs[]
QED

Theorem step_inner_unused_gas_nonincrease:
  s.contexts <> [] /\ step_inner s = (r,s') ==>
  unused_gas (MAP FST s'.contexts) <= unused_gas (MAP FST s.contexts)
Proof
  strip_tac >> mp_tac decreases_gas_cred_step_inner >>
  rewrite_tac[decreases_gas_cred_def] >>
  disch_then (qspec_then `s` mp_tac) >>
  simp[contexts_weight_def, LEX_DEF] >>
  Cases_on `r` >> gvs[] >> decide_tac
QED

Theorem step_unused_gas_nonincrease:
  s.contexts <> [] /\ step s = (r,s') ==>
  unused_gas (MAP FST s'.contexts) <= unused_gas (MAP FST s.contexts)
Proof
  strip_tac >> mp_tac decreases_gas_cred_step >>
  rewrite_tac[decreases_gas_cred_def] >>
  disch_then (qspec_then `s` mp_tac) >>
  simp[contexts_weight_def, LEX_DEF] >>
  Cases_on `r` >> gvs[] >> decide_tac
QED

Theorem gas_stack_ok_pop_transfer:
  gas_stack_ok s /\ s.contexts = child::parent::rest /\
  s'.contexts = new::rest /\
  unused_gas (MAP FST s'.contexts) <= unused_gas (MAP FST s.contexts) ==>
  gas_stack_ok s'
Proof
  simp[gas_stack_ok_def, unused_gas_def] >> strip_tac >> gvs[] >>
  qx_gen_tac `i` >> strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >>
  simp[EL_CONS, PRE_SUB1] >> decide_tac
QED

Theorem gas_stack_ok_push_transfer:
  gas_stack_ok s /\ s.contexts = old::rest /\
  s'.contexts = child::parent::rest' /\ MAP FST rest' = MAP FST rest /\
  unused_gas (MAP FST s'.contexts) <= unused_gas (MAP FST s.contexts) /\
  frame_unused_gas (FST child) <= (FST parent).gasUsed ==>
  gas_stack_ok s'
Proof
  simp[gas_stack_ok_def, unused_gas_def] >> strip_tac >> gvs[] >>
  qx_gen_tac `i` >> Cases_on `i` >> simp[] >>
  strip_tac >>
  `LENGTH rest' = LENGTH rest` by metis_tac[LENGTH_MAP] >>
  `FST (EL n rest') = FST (EL n rest)` by metis_tac[EL_MAP] >>
  `MAP FST (TAKE n rest') = MAP FST (TAKE n rest)` by metis_tac[MAP_TAKE] >>
  first_x_assum (qspec_then `n` mp_tac) >>
  simp[EL_CONS, PRE_SUB1] >> decide_tac
QED

Theorem gas_stack_ok_same_tail_transfer:
  gas_stack_ok s /\ s.contexts <> [] /\ s'.contexts <> [] /\
  MAP FST (TL s'.contexts) = MAP FST (TL s.contexts) /\
  unused_gas (MAP FST s'.contexts) <= unused_gas (MAP FST s.contexts) ==>
  gas_stack_ok s'
Proof
  strip_tac >> Cases_on `s.contexts` >> gvs[] >>
  Cases_on `s'.contexts` >> gvs[gas_stack_ok_def, unused_gas_def] >>
  qx_gen_tac `i` >> strip_tac >>
  `LENGTH t' = LENGTH t` by metis_tac[LENGTH_MAP] >>
  `FST (EL i t') = FST (EL i t)` by metis_tac[EL_MAP] >>
  `MAP FST (TAKE i t') = MAP FST (TAKE i t)` by metis_tac[MAP_TAKE] >>
  first_x_assum (qspec_then `i` mp_tac) >>
  simp[EL_CONS, PRE_SUB1] >> decide_tac
QED

Theorem inner_push_preserves_gas_stack_ok:
  wf_state s ∧ step_inner s = (r, s') ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
    gas_stack_ok s'
Proof
  strip_tac >>
  `s.contexts <> [] /\ gas_stack_ok s` by gvs[wf_state_def] >>
  drule_all step_inner_unused_gas_nonincrease >> strip_tac >>
  drule_all step_inner_grow_parent_unused_gas_ok >> strip_tac >>
  drule step_inner_push_structure >> simp[] >> strip_tac >>
  Cases_on `s.contexts` >> gvs[] >>
  Cases_on `s'.contexts` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  irule gas_stack_ok_push_transfer >>
  qexistsl_tac [`h'`, `h`, `h''`, `t`, `t''`, `s`] >> simp[]
QED

Theorem step_inner_preserves_stack_room_gas_ok:
  wf_state s ∧ step_inner s = (r, s') ⇒
    stack_room_ok s' ∧ gas_stack_ok s'
Proof
  strip_tac
  >> `s.contexts ≠ []` by gvs[wf_state_def]
  >> `LENGTH s'.contexts ≥ LENGTH s.contexts` by (
       mp_tac same_frame_or_grow_step_inner_named
       >> metis_tac[same_frame_or_grow_length])
  >> Cases_on `LENGTH s'.contexts = LENGTH s.contexts`
  >- (
    `same_frame_rel s s'` by (
       mp_tac same_frame_or_grow_step_inner_named
       >> metis_tac[same_frame_or_grow_eq_length])
    >> conj_tac
    >- metis_tac[same_frame_rel_preserves_stack_room_ok, wf_state_def]
    >> irule same_frame_rel_preserves_gas_stack_ok
    >> goal_assum $ drule_at Any
    >> gvs[wf_state_def]
    >> simp[GREATER_EQ]
    >> irule step_inner_same_frame_unused_gas_monotone
    >> simp[])
  >> `LENGTH s'.contexts > LENGTH s.contexts` by decide_tac
  >> metis_tac[inner_push_preserves_stack_room_ok
              ,inner_push_preserves_gas_stack_ok]
QED

Theorem step_pop_preserves_gas_stack_ok:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s'.contexts < LENGTH s.contexts ⇒
  gas_stack_ok s'
Proof
  strip_tac >>
  `s.contexts <> [] /\ gas_stack_ok s` by gvs[wf_state_def] >>
  drule_all step_unused_gas_nonincrease >> strip_tac >>
  drule step_pop_structure >> (impl_tac >- gvs[wf_state_def]) >>
  disch_then (qx_choosel_then [`new_head`, `parent`, `rest`] strip_assume_tac) >>
  Cases_on `s.contexts` >> gvs[] >>
  irule gas_stack_ok_pop_transfer >>
  goal_assum $ drule_at (Pat `gas_stack_ok`) >>
  goal_assum $ drule_at (Pat `s.contexts = _`) >> simp[]
QED

Theorem step_preserves_gas_stack_ok:
  wf_state s ⇒ gas_stack_ok (SND (step s))
Proof
  strip_tac >> Cases_on `step s` >> simp[] >>
  rename1 `step s = (_,s')` >> rename1 `step s = (r,s')` >>
  `s.contexts <> [] /\ gas_stack_ok s /\ outputTo_consistent_stack s` by
    gvs[wf_state_def] >>
  drule_all step_unused_gas_nonincrease >> strip_tac >>
  Cases_on `LENGTH s'.contexts = LENGTH s.contexts`
  >- (`outputTo_consistent s` by
        metis_tac[outputTo_consistent_stack_imp_consistent] >>
      drule_all step_same_frame >> strip_tac >>
      irule gas_stack_ok_same_tail_transfer >>
      (conj_tac >- (Cases_on `s.contexts` >> Cases_on `s'.contexts` >> gvs[])) >>
      qexists_tac `s` >>
      gvs[same_frame_rel_def] >> Cases_on `s.contexts` >> gvs[]) >>
  Cases_on `LENGTH s'.contexts > LENGTH s.contexts`
  >- (drule_all step_grow_parent_unused_gas_ok >> strip_tac >>
      drule step_push_structure >> simp[] >> strip_tac >>
      Cases_on `s.contexts` >> gvs[] >>
      Cases_on `s'.contexts` >> gvs[] >> Cases_on `t'` >> gvs[] >>
      irule gas_stack_ok_push_transfer >>
      qexistsl_tac [`h'`, `h`, `h''`, `t`, `t''`, `s`] >> simp[]) >>
  `LENGTH s'.contexts < LENGTH s.contexts` by decide_tac >>
  metis_tac[step_pop_preserves_gas_stack_ok]
QED

Theorem step_preserves_wf_state:
  wf_state s ⇒ wf_state (SND (step s))
Proof
  mp_tac decreases_gas_cred_step
  \\ mp_tac preserves_wf_accounts_step
  \\ mp_tac (GEN_ALL limits_num_contexts_step)
  \\ rewrite_tac[decreases_gas_cred_def, preserves_wf_accounts_def,
                 limits_num_contexts_def]
  \\ rw[wf_state_def]
  >- ( first_x_assum(qspec_then`s`mp_tac) \\ rw[] )
  >- ( `1026 = SUC 1025` by simp[] \\ metis_tac[LESS_EQ_IFF_LESS_SUC])
  >- ( first_x_assum(qspec_then`s`mp_tac) \\ rw[])
  >- ( irule step_preserves_stack_room_ok \\ simp[] \\ gvs[wf_state_def])
  >- ( irule step_preserves_gas_stack_ok \\ simp[] \\ gvs[wf_state_def])
  >- ( irule step_preserves_outputTo_consistent_stack \\ simp[] \\ gvs[wf_state_def])
QED

Theorem run_preserves_wf_state:
  wf_state s ∧ run s = SOME (r, s') ⇒ wf_state s'
Proof
  rpt strip_tac
  >> gvs[run_def]
  >> `(λp. wf_state (SND p)) (r, s')` suffices_by simp[]
  >> irule (MP_CANON OWHILE_INV_IND)
  >> goal_assum $ drule_at Any
  >> simp[]
  >> qx_gen_tac`s''`
  >> PairCases_on `s''`
  >> simp[]
  >> strip_tac
  >> Cases_on `step s''1`
  >> simp[]
  >> drule step_preserves_wf_state
  >> simp[]
QED

Theorem run_call_preserves_wf_state:
  wf_state es ∧ run_call es = SOME (r, es') ⇒ wf_state es'
Proof
  rpt strip_tac
  >> gvs[run_call_def]
  >> `(λp. wf_state (SND p)) (r, es')` suffices_by simp[]
  >> irule (MP_CANON OWHILE_INV_IND)
  >> goal_assum $ drule_at Any
  >> simp[]
  >> qx_gen_tac`s`
  >> PairCases_on `s`
  >> simp[]
  >> strip_tac
  >> Cases_on `step s1`
  >> simp[]
  >> drule step_preserves_wf_state
  >> simp[]
QED

(* The rollback projections of a same-frame prefix are literally equal. *)
Theorem same_frame_saved_prefix:
  same_frame_rel s t ==>
  !n. MAP SND (TAKE n t.contexts) = MAP SND (TAKE n s.contexts) /\
      MAP (\p. (FST p).msgParams) (TAKE n t.contexts) =
      MAP (\p. (FST p).msgParams) (TAKE n s.contexts)
Proof
  rw[same_frame_rel_def]
  >> Cases_on `s.contexts` >> Cases_on `t.contexts` >> gvs[]
  >> Cases_on `n` >> simp[]
QED

Theorem active_rollbacks_same_frame_transport:
  same_frame_rel s t /\ EVERY P (active_rollbacks d s) /\ P t.rollback ==>
  EVERY P (active_rollbacks d t)
Proof
  strip_tac >> drule same_frame_saved_prefix >> strip_tac
  >> gvs[active_rollbacks_def, same_frame_rel_def]
QED

(* A pop consumes the first saved rollback. The surviving saved prefix is
   unchanged, even when the pop exits below the entry depth. *)
Theorem saved_prefix_pop_transport:
  EVERY P (MAP SND (TAKE (SUC n) (child :: parent :: rest))) ==>
  EVERY P (MAP SND (TAKE n ((new_head,SND parent) :: rest)))
Proof
  Cases_on `n` >> simp[]
QED

Theorem active_rollbacks_pop_transport:
  s.contexts = child :: parent :: rest /\
  t.contexts = (new_head,SND parent) :: rest /\
  EVERY P (active_rollbacks d s) /\ P t.rollback ==>
  EVERY P (active_rollbacks d t)
Proof
  strip_tac >> gvs[active_rollbacks_def]
  >> Cases_on `LENGTH rest + 2 < MAX 2 d`
  >- (`SUC (SUC (LENGTH rest)) - MAX 2 d = 0` by decide_tac >> simp[])
  >> `SUC (SUC (SUC (LENGTH rest))) - MAX 2 d =
        SUC (SUC (SUC (LENGTH rest)) - MAX 2 d)` by decide_tac
  >> gvs[] >> irule saved_prefix_pop_transport >> qexists_tac `child` >> simp[]
QED

Theorem protected_rollbacks_pop_transport:
  s.contexts = child :: parent :: rest /\
  t.contexts = (new_head,SND parent) :: rest /\
  d <= LENGTH t.contexts /\
  EVERY P (s.rollback :: MAP SND (TAKE (LENGTH s.contexts - d) s.contexts)) /\
  P t.rollback ==>
  EVERY P (t.rollback :: MAP SND (TAKE (LENGTH t.contexts - d) t.contexts))
Proof
  strip_tac >> gvs[]
  >> `SUC (SUC (LENGTH rest)) - d = SUC (SUC (LENGTH rest) - d)` by decide_tac
  >> gvs[] >> irule saved_prefix_pop_transport >> qexists_tac `child` >> simp[]
  >> `SUC (SUC (LENGTH rest)) - (d + 1) = SUC (LENGTH rest) - d` by decide_tac
  >> gvs[]
QED

(* Relational transport from the old active rollback followed by its saved
   prefix to the newly saved prefix. Consumers use EVERY, not EL arithmetic. *)
Theorem saved_prefix_push_transport:
  n < LENGTH (cs:(context # rollback_state) list) /\ SUC n <= LENGTH cs' /\
  EVERY P ((rb:rollback_state) :: MAP SND (TAKE n cs)) /\
  (!i. i < SUC n ==>
       R (if i = 0 then rb else SND (EL (i-1) cs)) (SND (EL i cs'))) /\
  (!x y. P x /\ R x y ==> Q y) ==>
  EVERY Q (MAP SND (TAKE (SUC n) cs'))
Proof
  strip_tac
  >> fs[EVERY_EL, EL_MAP, LENGTH_TAKE_EQ]
  >> qx_gen_tac `i` >> strip_tac
  >> simp[EL_TAKE]
  >> first_x_assum irule
  >> qexists_tac `if i = 0 then rb else SND (EL (i-1) cs)`
  >> conj_tac
  >- (Cases_on `i` >> gvs[EL_TAKE, ADD1])
  >> first_x_assum irule >> simp[]
QED

Theorem active_rollbacks_push_transport:
  0 < d /\ d <= LENGTH s.contexts /\
  LENGTH t.contexts = SUC (LENGTH s.contexts) /\
  EVERY P (active_rollbacks d s) /\ Q t.rollback /\
  (!i. i < LENGTH s.contexts ==>
       R (if i = 0 then s.rollback else SND (EL (i-1) s.contexts))
         (SND (EL i t.contexts))) /\
  (!x y. P x /\ R x y ==> Q y) ==>
  EVERY Q (active_rollbacks d t)
Proof
  strip_tac
  >> `SUC (LENGTH t.contexts) - MAX 2 d =
        SUC (SUC (LENGTH s.contexts) - MAX 2 d)` by
       (rw[MAX_DEF] >> decide_tac)
  >> `SUC (LENGTH s.contexts) - MAX 2 d < LENGTH s.contexts` by
       (rw[MAX_DEF] >> decide_tac)
  >> gvs[active_rollbacks_def]
  >> irule saved_prefix_push_transport
  >> conj_tac >- simp[]
  >> qexistsl_tac [`P`, `R`, `s.contexts`, `s.rollback`] >> simp[]
  >> metis_tac[]
QED

Theorem protected_rollbacks_same_frame_transport:
  same_frame_rel s t /\
  EVERY P (s.rollback :: MAP SND (TAKE (LENGTH s.contexts - d) s.contexts)) /\
  P t.rollback ==>
  EVERY P (t.rollback :: MAP SND (TAKE (LENGTH t.contexts - d) t.contexts))
Proof
  strip_tac >> drule same_frame_saved_prefix >> strip_tac
  >> gvs[same_frame_rel_def]
QED

Theorem protected_rollbacks_push_transport:
  0 < d /\ d <= LENGTH s.contexts /\
  LENGTH t.contexts = SUC (LENGTH s.contexts) /\
  EVERY P (s.rollback :: MAP SND (TAKE (LENGTH s.contexts - d) s.contexts)) /\
  Q t.rollback /\
  (!i. i < LENGTH s.contexts ==>
       R (if i = 0 then s.rollback else SND (EL (i-1) s.contexts))
         (SND (EL i t.contexts))) /\
  (!x y. P x /\ R x y ==> Q y) ==>
  EVERY Q (t.rollback :: MAP SND (TAKE (LENGTH t.contexts - d) t.contexts))
Proof
  strip_tac
  >> `LENGTH t.contexts - d = SUC (LENGTH s.contexts - d)` by decide_tac
  >> `LENGTH s.contexts - d < LENGTH s.contexts` by decide_tac
  >> simp[] >> irule saved_prefix_push_transport
  >> conj_tac >- simp[]
  >> qexistsl_tac [`P`, `R`, `s.contexts`, `s.rollback`] >> simp[]
  >> metis_tac[]
QED

Theorem protected_frames_same_frame_transport:
  same_frame_rel s t /\
  EVERY P (MAP (\p. (FST p).msgParams) (TAKE (LENGTH s.contexts - d) s.contexts)) ==>
  EVERY P (MAP (\p. (FST p).msgParams) (TAKE (LENGTH t.contexts - d) t.contexts))
Proof
  strip_tac >> drule same_frame_saved_prefix >> strip_tac
  >> gvs[same_frame_rel_def]
QED

Theorem protected_frames_pop_transport:
  s.contexts = child :: parent :: rest /\
  t.contexts = (new_head,SND parent) :: rest /\
  new_head.msgParams = (FST parent).msgParams /\
  d <= LENGTH t.contexts /\
  EVERY P (MAP (\p. (FST p).msgParams) (TAKE (LENGTH s.contexts - d) s.contexts)) ==>
  EVERY P (MAP (\p. (FST p).msgParams) (TAKE (LENGTH t.contexts - d) t.contexts))
Proof
  strip_tac >> gvs[]
  >> `SUC (SUC (LENGTH rest)) - d = SUC (SUC (LENGTH rest) - d)` by decide_tac
  >> `SUC (SUC (LENGTH rest)) - (d+1) = SUC (LENGTH rest) - d` by decide_tac
  >> gvs[] >> Cases_on `SUC (LENGTH rest) - d` >> gvs[]
QED

Theorem protected_frames_push_transport:
  0 < d /\ d <= LENGTH s.contexts /\
  LENGTH t.contexts = SUC (LENGTH s.contexts) /\
  MAP FST (TL (TL t.contexts)) = MAP FST (TL s.contexts) /\
  (FST (EL 1 t.contexts)).msgParams = (FST (HD s.contexts)).msgParams /\
  P (FST (HD t.contexts)).msgParams /\
  EVERY P (MAP (\p. (FST p).msgParams) (TAKE (LENGTH s.contexts - d) s.contexts)) ==>
  EVERY P (MAP (\p. (FST p).msgParams) (TAKE (LENGTH t.contexts - d) t.contexts))
Proof
  strip_tac
  >> `LENGTH t.contexts - d = SUC (LENGTH s.contexts - d)` by decide_tac
  >> Cases_on `s.contexts` >> gvs[]
  >> Cases_on `t.contexts` >> gvs[]
  >> rename1 `t.contexts = child :: cs`
  >> Cases_on `cs` >> gvs[]
  >> rename1 `t.contexts = child :: parent :: rest`
  >> `MAP (\c:context. c.msgParams) (MAP FST rest) =
      MAP (\c:context. c.msgParams) (MAP FST t')` by simp[]
  >> gvs[MAP_MAP_o, combinTheory.o_DEF]
  >> `!n. MAP (\p. (FST p).msgParams) (TAKE n rest) =
            MAP (\p. (FST p).msgParams) (TAKE n t')`
      by simp[MAP_TAKE]
  >> Cases_on `SUC (LENGTH t') - d` >> gvs[]
  >- (`SUC (SUC (LENGTH t')) - (d+1) = 0` by decide_tac >> simp[])
  >> `SUC (SUC (LENGTH t')) - (d+2) = n` by decide_tac >> simp[]
QED

(* Both rollback choices in step_pop_structure come from the old active
   list. In particular this remains true at d=1 and at an exit below d. *)
Theorem active_rollbacks_pop_sources:
  d <= LENGTH s.contexts /\ 2 <= LENGTH s.contexts ==>
  MEM s.rollback (active_rollbacks d s) /\
  MEM (SND (HD s.contexts)) (active_rollbacks d s)
Proof
  strip_tac
  >> `0 < SUC (LENGTH s.contexts) - MAX 2 d` by
       (rw[MAX_DEF] >> decide_tac)
  >> Cases_on `SUC (LENGTH s.contexts) - MAX 2 d` >> gvs[]
  >> Cases_on `s.contexts` >> gvs[active_rollbacks_def]
QED

(* No collision protection is required for an unchanged-storage transition:
   this is the interface used for either rollback choice of a pop. *)
Theorem storage_slots_access_transport:
  (!a k. ~fIN (SK a k) rb.accesses.storageKeys ==>
     lookup_storage k (lookup_account a rb.accounts).storage =
       lookup_storage k (lookup_account a rb0.accounts).storage \/
     lookup_storage k (lookup_account a rb.accounts).storage = 0w /\
       ~account_already_created (lookup_account a rb0.accounts)) /\
  toSet rb.accesses.storageKeys SUBSET toSet next.accesses.storageKeys /\
  (!a. (lookup_account a next.accounts).storage =
       (lookup_account a rb.accounts).storage) ==>
  !a k. ~fIN (SK a k) next.accesses.storageKeys ==>
     lookup_storage k (lookup_account a next.accounts).storage =
       lookup_storage k (lookup_account a rb0.accounts).storage \/
     lookup_storage k (lookup_account a next.accounts).storage = 0w /\
       ~account_already_created (lookup_account a rb0.accounts)
Proof
  rpt strip_tac
  >> `~fIN (SK a k) rb.accesses.storageKeys` by
       (gvs[SUBSET_DEF, finite_setTheory.fIN_IN] >> metis_tac[])
  >> metis_tac[]
QED

(* Slot safety composes across access inclusion and a possible CREATE clear.
   Collision protection is needed only for the clearing alternative. *)
Theorem storage_slots_compose:
  (!a k. ~fIN (SK a k) rb.accesses.storageKeys ==>
     lookup_storage k (lookup_account a rb.accounts).storage =
       lookup_storage k (lookup_account a rb0.accounts).storage \/
     lookup_storage k (lookup_account a rb.accounts).storage = 0w /\
       ~account_already_created (lookup_account a rb0.accounts)) /\
  toSet rb.accesses.storageKeys SUBSET toSet next.accesses.storageKeys /\
  (!a k. ~fIN (SK a k) next.accesses.storageKeys ==>
     lookup_storage k (lookup_account a next.accounts).storage =
       lookup_storage k (lookup_account a rb.accounts).storage \/
     lookup_storage k (lookup_account a next.accounts).storage = 0w /\
       ~account_already_created (lookup_account a rb.accounts)) /\
  (!a. account_already_created (lookup_account a rb0.accounts) ==>
       account_already_created (lookup_account a rb.accounts)) ==>
  !a k. ~fIN (SK a k) next.accesses.storageKeys ==>
     lookup_storage k (lookup_account a next.accounts).storage =
       lookup_storage k (lookup_account a rb0.accounts).storage \/
     lookup_storage k (lookup_account a next.accounts).storage = 0w /\
       ~account_already_created (lookup_account a rb0.accounts)
Proof
  rpt strip_tac
  >> `~fIN (SK a k) rb.accesses.storageKeys` by
       (gvs[SUBSET_DEF, finite_setTheory.fIN_IN] >> metis_tac[])
  >> first_x_assum (qspecl_then [`a`, `k`] strip_assume_tac)
  >> metis_tac[]
QED

(* Nonce/code transport before the return-code deposit boundary. *)
val nonce_code_rel = ``\a (s:execution_state) (t:execution_state).
  (lookup_account a s.rollback.accounts).nonce <=
    (lookup_account a t.rollback.accounts).nonce /\
  (lookup_account a t.rollback.accounts).code =
    (lookup_account a s.rollback.accounts).code``;

Theorem nonce_code_rel_trans:
  ^nonce_code_rel a s u /\ ^nonce_code_rel a u t ==> ^nonce_code_rel a s t
Proof
  simp[] >> strip_tac >> simp[] >> decide_tac
QED

Theorem preserves_nonce_code_of_rollback:
  preserves_rollback m ==> preserves (^nonce_code_rel a) m
Proof
  rw[preserves_rollback_def, preserves_def] >>
  first_x_assum drule >> simp[]
QED

Theorem preserves_nonce_code_bind:
  preserves (^nonce_code_rel a) g /\
  (!x. preserves (^nonce_code_rel a) (f x)) ==>
  preserves (^nonce_code_rel a) (bind g f)
Proof
  strip_tac >> irule preserves_bind >> simp[] >>
  metis_tac[nonce_code_rel_trans]
QED

Theorem preserves_nonce_code_ignore_bind:
  preserves (^nonce_code_rel a) g /\
  preserves (^nonce_code_rel a) f ==>
  preserves (^nonce_code_rel a) (ignore_bind g f)
Proof
  strip_tac >> irule preserves_ignore_bind >> simp[] >>
  metis_tac[nonce_code_rel_trans]
QED

Theorem preserves_nonce_code_increment:
  preserves (^nonce_code_rel a) (update_accounts (increment_nonce b))
Proof
  rw[preserves_def, update_accounts_def, return_def,
     increment_nonce_lookup, increment_nonce_code] >>
  Cases_on `a = b` >> gvs[]
QED

Theorem preserves_nonce_code_transfer:
  preserves (^nonce_code_rel a)
    (update_accounts (transfer_value sender recipient value))
Proof
  rw[preserves_def, update_accounts_def, return_def,
     transfer_value_preserves_code, transfer_value_preserves_nonce]
QED

Theorem preserves_nonce_code_proceed_create:
  preserves (^nonce_code_rel a)
    (proceed_create sender address value code gas)
Proof
  rw[preserves_def, proceed_create_def, bind_def, ignore_bind_def,
       get_accounts_def, drain_state_gas_reservoir_def,
       get_current_context_def, set_current_context_def,
       update_accounts_def, get_rollback_def, get_original_def,
       set_original_def, push_context_def, return_def, fail_def,
       COND_RATOR, AllCaseEqs(),
       increment_nonce_lookup, increment_nonce_code,
       transfer_value_preserves_code, transfer_value_preserves_nonce] >>
  Cases_on `a = address` >> Cases_on `a = sender` >>
  gvs[increment_nonce_lookup, increment_nonce_code,
      transfer_value_preserves_code, transfer_value_preserves_nonce]
QED

Theorem preserves_nonce_code_access_address:
  preserves (^nonce_code_rel a) (access_address b)
Proof
  rw[preserves_def, access_address_def, domain_check_def,
     set_domain_def, return_def, fail_def, AllCaseEqs()] >>
  gvs[ignore_bind_def, bind_def, set_domain_def, return_def]
QED

Theorem preserves_nonce_code_step_create:
  preserves (^nonce_code_rel a) (step_create two)
Proof
  simp[step_create_def, ignore_bind_def] >>
  rpt (ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
       (conj_tac >-
         (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
       simp[] >> rpt gen_tac) >>
  IF_CASES_TAC
  >- (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[]) >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >- simp[SRULE [] preserves_nonce_code_access_address]) >>
  simp[] >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >-
    (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
  simp[] >>
  ntac 2
    (ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
     (conj_tac >-
       (irule (SRULE [] preserves_nonce_code_of_rollback) >>
        simp[preserves_rollback_state_gas_meter])) >>
     simp[] >> rpt gen_tac) >>
  IF_CASES_TAC
  >- (simp[abort_create_exists_def, ignore_bind_def] >>
      ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
      (conj_tac >- simp[SRULE [] preserves_nonce_code_increment]) >>
      simp[] >> irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[]) >>
  simp[SRULE [] preserves_nonce_code_proceed_create]
QED

Theorem preserves_nonce_code_proceed_call:
  preserves (^nonce_code_rel a)
    (proceed_call op sender address value off sz code gas output)
Proof
  simp[proceed_call_def, ignore_bind_def] >>
  ntac 4
    (ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
     (conj_tac >-
       (irule (SRULE [] preserves_nonce_code_of_rollback) >>
        simp[preserves_rollback_state_gas_meter])) >>
     gen_tac) >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >-
    (IF_CASES_TAC >- simp[SRULE [] preserves_nonce_code_transfer] >>
     irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
  simp[] >>
  rpt (ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
       (conj_tac >-
         (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
       simp[] >> rpt gen_tac) >>
  irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[]
QED

Theorem preserves_nonce_code_step_call:
  preserves (^nonce_code_rel a) (step_call op)
Proof
  simp[step_call_def, ignore_bind_def] >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >-
    (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
  gen_tac >> pairarg_tac >> simp[] >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >-
    (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >> gen_tac >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >- simp[SRULE [] preserves_nonce_code_access_address]) >> gen_tac >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >-
    (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >> gen_tac >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >-
    (Cases_on `get_delegate (lookup_account (w2w (EL 1 args)) accounts).code`
     >- (simp[] >> irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[]) >>
     simp[] >> ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
     (conj_tac >- simp[SRULE [] preserves_nonce_code_access_address]) >>
     gen_tac >> irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
  Cases >> simp[] >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >-
    (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
  gen_tac >>
  ntac 3
    (ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
     (conj_tac >-
       (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
     gen_tac) >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >-
    (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
  gen_tac >> pairarg_tac >> simp[] >>
  rpt (ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
       (conj_tac >-
         (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
       simp[] >> rpt gen_tac) >>
  IF_CASES_TAC
  >- (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[]) >>
  rpt (ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
       (conj_tac >-
         (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
       simp[] >> rpt gen_tac) >>
  IF_CASES_TAC
  >- (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[]) >>
  simp[SRULE [] preserves_nonce_code_proceed_call]
QED

Theorem preserves_nonce_code_access_slot:
  preserves (^nonce_code_rel a) (access_slot sk)
Proof
  rw[preserves_def, access_slot_def, domain_check_def,
     set_domain_def, return_def, fail_def, AllCaseEqs()] >>
  gvs[ignore_bind_def, bind_def, set_domain_def, return_def]
QED

Theorem preserves_nonce_code_write_storage:
  preserves (^nonce_code_rel a) (write_storage b k v)
Proof
  rw[preserves_def, write_storage_def, update_accounts_def, return_def] >>
  Cases_on `a = b` >>
  gvs[lookup_account_def, update_account_def, APPLY_UPDATE_THM]
QED

Theorem preserves_nonce_code_sstore_gas:
  preserves (^nonce_code_rel a) (step_sstore_gas_consumption b k v)
Proof
  simp[step_sstore_gas_consumption_def, ignore_bind_def] >>
  rpt (ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
       (conj_tac >-
         (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
       simp[] >> rpt gen_tac) >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >- simp[SRULE [] preserves_nonce_code_access_slot]) >> gen_tac >>
  irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[]
QED

Theorem preserves_nonce_code_step_sstore:
  preserves (^nonce_code_rel a) (step_sstore transient)
Proof
  simp[step_sstore_def, ignore_bind_def] >>
  ntac 2
    (ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
     (conj_tac >-
       (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >> gen_tac) >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >-
    (Cases_on `transient` >> simp[SRULE [] preserves_nonce_code_sstore_gas] >>
     irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
  simp[] >> ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >-
    (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >> simp[] >>
  Cases_on `transient` >> simp[SRULE [] preserves_nonce_code_write_storage] >>
  rw[preserves_def, write_transient_storage_def, bind_def,
     get_tStorage_def, set_tStorage_def, return_def]
QED

Theorem self_destruct_account_update_nonce_code:
  (lookup_account a
    (update_account sender ((lookup_account sender accounts) with balance := 0)
      (transfer_value sender address value accounts))).nonce =
    (lookup_account a accounts).nonce /\
  (lookup_account a
    (update_account sender ((lookup_account sender accounts) with balance := 0)
      (transfer_value sender address value accounts))).code =
    (lookup_account a accounts).code
Proof
  Cases_on `a = sender` >>
  simp[lookup_account_def, update_account_def, combinTheory.APPLY_UPDATE_THM] >>
  simp[GSYM lookup_account_def, transfer_value_preserves_nonce,
       transfer_value_preserves_code]
QED

Theorem preserves_nonce_code_step_self_destruct:
  preserves (^nonce_code_rel a) step_self_destruct
Proof
  simp[step_self_destruct_def] >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >- (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
  gen_tac >> ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >- simp[SRULE [] preserves_nonce_code_access_address]) >>
  gen_tac >> ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >- (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
  gen_tac >> simp[ignore_bind_def] >>
  rpt (ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
       (conj_tac >-
         (irule (SRULE [] preserves_nonce_code_of_rollback) >> simp[])) >>
       simp[] >> rpt gen_tac) >>
  ho_match_mp_tac (SRULE [] preserves_nonce_code_bind) >>
  (conj_tac >- simp[SRULE [] preserves_nonce_code_transfer]) >>
  simp[] >>
  rw[preserves_def, bind_def, push_logs_def, get_original_def,
     get_current_context_def, set_current_context_def, add_to_delete_def,
     finish_def, return_def, fail_def, COND_RATOR, AllCaseEqs()] >>
  gvs[add_to_delete_def, return_def]
QED

Theorem cp_nonce_code:
  cp (m:unit execution) ==> preserves_when (\s. s.contexts <> []) (^nonce_code_rel a) m
Proof
  rw[cp_def, preserves_when_def] >>
  first_x_assum drule_all >> simp[]
QED

Theorem step_inst_nonce_code:
  s.contexts <> [] /\ step_inst op s = (r,t) ==> ^nonce_code_rel a s t
Proof
  Cases_on `op`
  >~ [`step_inst SStore`] >-
    (simp[step_inst_def] >> strip_tac >>
     drule (SRULE [preserves_def] preserves_nonce_code_step_sstore) >> simp[])
  >~ [`step_inst TStore`] >-
    (simp[step_inst_def] >> strip_tac >>
     drule (SRULE [preserves_def] preserves_nonce_code_step_sstore) >> simp[])
  >~ [`step_inst SelfDestruct`] >-
    (simp[step_inst_def] >> strip_tac >>
     drule (SRULE [preserves_def] preserves_nonce_code_step_self_destruct) >> simp[])
  >~ [`step_inst Create`] >-
    (simp[step_inst_def] >> strip_tac >>
     drule (SRULE [preserves_def] preserves_nonce_code_step_create) >> simp[])
  >~ [`step_inst Create2`] >-
    (simp[step_inst_def] >> strip_tac >>
     drule (SRULE [preserves_def] preserves_nonce_code_step_create) >> simp[])
  >~ [`step_inst Call`] >-
    (simp[step_inst_def] >> strip_tac >>
     drule (SRULE [preserves_def] preserves_nonce_code_step_call) >> simp[])
  >~ [`step_inst CallCode`] >-
    (simp[step_inst_def] >> strip_tac >>
     drule (SRULE [preserves_def] preserves_nonce_code_step_call) >> simp[])
  >~ [`step_inst DelegateCall`] >-
    (simp[step_inst_def] >> strip_tac >>
     drule (SRULE [preserves_def] preserves_nonce_code_step_call) >> simp[])
  >~ [`step_inst StaticCall`] >-
    (simp[step_inst_def] >> strip_tac >>
     drule (SRULE [preserves_def] preserves_nonce_code_step_call) >> simp[])
  >~ [`step_inst (Log n)`] >- (
    strip_tac >>
    `preserves (^nonce_code_rel a) (step_inst (Log n))` by
      (irule preserves_nonce_code_of_rollback >>
       irule step_inst_Log_preserves_rollback) >>
    gvs[preserves_def] >> first_x_assum drule >> simp[]) >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `m s = (r,t)` >>
  irule (SRULE [preserves_when_def] cp_nonce_code) >>
  simp[] >> qexistsl_tac [`m`,`r`] >> simp[Abbr `m`]
QED

Theorem same_frame_nonce_monotone:
  same_frame_rel s t ==>
  (lookup_account a s.rollback.accounts).nonce <=
    (lookup_account a t.rollback.accounts).nonce
Proof
  rw[same_frame_rel_def, callee_local_changes_def] >>
  Cases_on `a = (FST (HD s.contexts)).msgParams.callee` >> gvs[]
QED

Theorem step_same_frame_positive_nonce:
  wf_state s /\ step s = (r, t) /\
  LENGTH t.contexts = LENGTH s.contexts /\
  0 < (lookup_account a s.rollback.accounts).nonce ==>
  0 < (lookup_account a t.rollback.accounts).nonce
Proof
  strip_tac >>
  `outputTo_consistent s` by
    metis_tac[outputTo_consistent_stack_imp_consistent, wf_state_def] >>
  drule_all step_same_frame >> strip_tac >>
  drule same_frame_nonce_monotone >>
  disch_then (qspec_then `a` assume_tac) >> gvs[] >> decide_tac
QED

Theorem deposit_code_nonce:
  (lookup_account a
    (update_account b (lookup_account b accounts with code := code)
      accounts)).nonce = (lookup_account a accounts).nonce
Proof
  rw[lookup_account_def, update_account_def, APPLY_UPDATE_THM]
QED

Theorem deposit_code_other:
  a <> b ==>
  lookup_account a
    (update_account b (lookup_account b accounts with code := code)
      accounts) = lookup_account a accounts
Proof
  simp[lookup_account_def, update_account_def, APPLY_UPDATE_THM]
QED

Theorem handle_create_nonce:
  s.contexts <> [] /\ handle_create e s = (r, t) ==>
  (lookup_account a t.rollback.accounts).nonce =
    (lookup_account a s.rollback.accounts).nonce
Proof
  rw[handle_create_def, bind_def, get_return_data_def,
     get_output_to_def, get_current_context_def, return_def] >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >> gvs[] >>
  Cases_on `e` >> Cases_on `h0.msgParams.outputTo` >>
  gvs[reraise_def, ignore_bind_def, bind_def, assert_def,
      return_def, fail_def, AllCaseEqs(), consume_gas_def,
      get_current_context_def, set_current_context_def,
      update_accounts_def, deposit_code_nonce] >>
  drule (REWRITE_RULE [preserves_rollback_def]
    (CONJUNCT1 (CONJUNCT2 preserves_rollback_state_gas_meter))) >> simp[]
QED

Theorem handle_create_code_other:
  s.contexts <> [] /\ handle_create e s = (r,t) /\
  (FST (HD s.contexts)).msgParams.outputTo <> Code a ==>
  (lookup_account a t.rollback.accounts).code =
    (lookup_account a s.rollback.accounts).code
Proof
  rw[handle_create_def, bind_def, get_return_data_def,
     get_output_to_def, get_current_context_def, return_def] >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >> gvs[] >>
  Cases_on `e` >> Cases_on `h0.msgParams.outputTo` >>
  gvs[reraise_def, ignore_bind_def, bind_def, assert_def,
      return_def, fail_def, AllCaseEqs(), consume_gas_def,
      get_current_context_def, set_current_context_def,
      update_accounts_def, deposit_code_other] >>
  drule (REWRITE_RULE [preserves_rollback_def]
    (CONJUNCT1 (CONJUNCT2 preserves_rollback_state_gas_meter))) >> simp[deposit_code_other]
QED

Theorem handle_create_protected_account:
  s.contexts <> [] /\ handle_create e s = (r,t) /\
  ((lookup_account a s.rollback.accounts).nonce <> 0 \/
   ~NULL (lookup_account a s.rollback.accounts).code) /\
  ((FST (HD s.contexts)).msgParams.outputTo = Code a ==>
    0 < (lookup_account a s.rollback.accounts).nonce) ==>
  (lookup_account a t.rollback.accounts).nonce <> 0 \/
    ~NULL (lookup_account a t.rollback.accounts).code
Proof
  strip_tac >> drule_all handle_create_nonce >>
  disch_then (qspec_then `a` assume_tac) >>
  Cases_on `(FST (HD s.contexts)).msgParams.outputTo = Code a` >>
  gvs[] >> drule_all handle_create_code_other >> simp[]
QED

Theorem step_grow_dispatch:
  wf_state s /\ step s = (r,s') /\ LENGTH s.contexts < LENGTH s'.contexts ==>
  r = INL () /\
  ((?op. step_call op s = (INL (),s')) \/
   (?two. step_create two s = (INL (),s')))
Proof
  strip_tac
  >> `s.contexts <> []` by gvs[wf_state_def]
  >> qpat_x_assum `step s = _` mp_tac
  >> simp[step_def, handle_def]
  >> qmatch_goalsub_abbrev_tac `inner s`
  >> Cases_on `inner s` >> Cases_on `q`
  >- (simp[] >> strip_tac >> gvs[]
      >> gvs[Abbr `inner`, bind_def, AllCaseEqs()]
      >> gvs[get_current_context_def, return_def, fail_def, bind_def]
      >> gvs[option_CASE_rator, CaseEq "option", COND_RATOR, CaseEq "bool"]
      >~ [`step_inst Stop`]
      >- (drule_at Any psf_imp_length_contexts_preserved >> simp[])
      >~ [`step_inst Invalid`]
      >- (drule_at Any psf_imp_length_contexts_preserved >> simp[])
      >> gvs[ignore_bind_def, bind_def, AllCaseEqs()]
      >> rename1 `step_inst op s = (INL (),mid)`
      >> drule_at Any psf_imp_length_contexts_preserved >> simp[]
      >> (impl_keep_tac >- (strip_tac >>
          gvs[inc_pc_or_jump_def, COND_RATOR, AllCaseEqs(), return_def,
              bind_def, get_current_context_def, fail_def]))
      >> strip_tac
      >> `LENGTH s.contexts < LENGTH mid.contexts` by simp[]
      >> `is_call op` by (irule step_inst_inl_grew_is_call
          >> qexistsl_tac [`s`, `mid`] >> simp[])
      >> gvs[inc_pc_or_jump_def, return_def, COND_RATOR, CaseEq "bool"]
      >> Cases_on `op` >> gvs[is_call_def, step_inst_def]
      >> metis_tac[])
  >> simp[] >> strip_tac
  >> `same_frame_or_grow inner` by simp[Abbr `inner`]
  >> `LENGTH r'.contexts >= LENGTH s.contexts` by
      (drule_all same_frame_or_grow_length >> simp[])
  >> `r'.contexts <> []` by (strip_tac >> gvs[] >> Cases_on `s.contexts` >> gvs[])
  >> `LENGTH s'.contexts <= LENGTH s.contexts` suffices_by gvs[]
  >> Cases_on `LENGTH r'.contexts = LENGTH s.contexts`
  >- (drule handle_step_shrinks_by_one >> simp[])
  >> `LENGTH r'.contexts > LENGTH s.contexts` by simp[]
  >> `outputTo_consistent s` by
      (irule outputTo_consistent_stack_imp_consistent >> gvs[wf_state_def])
  >> `~vfm_abort y` by (irule step_inner_inr_grow_not_abort
      >> qexistsl_tac [`s`, `r'`] >> simp[Abbr `inner`])
  >> `0 < LENGTH s.contexts` by (Cases_on `s.contexts` >> gvs[])
  >> `LENGTH r'.contexts >= 2` by simp[]
  >> `LENGTH r'.contexts = LENGTH s.contexts + 1` by
      (qunabbrev_tac `inner` >> drule_then drule step_inner_grows_by_exactly_one >> gvs[])
  >> drule_at (Pat `handle_step`) handle_step_not_abort_pops >> gvs[]
  >> `decreases_gas_cred T 0 0 inner` suffices_by
      (gvs[decreases_gas_cred_def]
       >> disch_then (qspec_then `s` mp_tac) >> rw[]
       >> gvs[wf_state_def, EVERY_MEM])
  >> simp[Abbr `inner`]
  >> irule decreases_gas_cred_bind_mono
  >> qexistsl_tac [`T`, `F`] >> simp[] >> gen_tac
  >> rw[] >> CASE_TAC >> rw[]
  >> irule decreases_gas_cred_ignore_bind_mono >> rw[]
  >> qexistsl_tac [`F`, `T`] >> simp[]
QED

Theorem step_growth_nonce_code:
  wf_state s /\ step s = (r,t) /\ LENGTH s.contexts < LENGTH t.contexts ==>
  ^nonce_code_rel a s t
Proof
  strip_tac >> drule_all step_grow_dispatch >> strip_tac
  >- (drule (SRULE [preserves_def] preserves_nonce_code_step_call) >> simp[]) >>
  drule (SRULE [preserves_def] preserves_nonce_code_step_create) >> simp[]
QED

(* Protection starts with no newly introduced snapshots or Code frames. *)
Theorem collision_protection_initial:
  EVERY (\rb. !a.
    account_already_created (lookup_account a s.rollback.accounts) ==>
    account_already_created (lookup_account a rb.accounts))
    (s.rollback :: MAP SND (TAKE (LENGTH s.contexts - LENGTH s.contexts) s.contexts)) /\
  EVERY (\cr. !a. (FST cr).msgParams.outputTo = Code a ==>
    ~account_already_created (lookup_account a s.rollback.accounts))
    (TAKE (LENGTH s.contexts - LENGTH s.contexts) s.contexts)
Proof
  simp[]
QED

Theorem step_inst_preserves_created_account:
  s.contexts <> [] /\ step_inst op s = (r,t) /\
  account_already_created (lookup_account a s.rollback.accounts) ==>
  account_already_created (lookup_account a t.rollback.accounts)
Proof
  strip_tac >> drule_all step_inst_nonce_code >>
  disch_then (qspec_then `a` mp_tac) >>
  gvs[account_already_created_def] >> decide_tac
QED

Theorem handle_create_preserves_other_created_account:
  s.contexts <> [] /\ handle_create e s = (r,t) /\
  (FST (HD s.contexts)).msgParams.outputTo <> Code a /\
  account_already_created (lookup_account a s.rollback.accounts) ==>
  account_already_created (lookup_account a t.rollback.accounts)
Proof
  strip_tac >> drule_all handle_create_nonce >>
  disch_then (qspec_then `a` assume_tac) >>
  drule_all handle_create_code_other >>
  gvs[account_already_created_def]
QED

Theorem call_prefix_delegate_code_selection:
  preserves_when (\s. s.contexts <> [])
    (\s t. cp_rel s t /\ t.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys)
    (case get_delegate bytecode of
       NONE => return (bytecode, 0)
     | SOME d => do
         cost <- access_address d;
         return ((lookup_account d accounts).code, cost)
       od)
Proof
  Cases_on `get_delegate bytecode` >> simp[call_prefix_leaves]
  >> irule call_prefix_bind >> simp[call_prefix_leaves]
QED

Theorem credited_abort_call_value_length[local]:
  s.contexts <> [] /\
  ignore_bind (credit_new_account charged) (abort_call_value gas) s = (r,t) ==>
  LENGTH t.contexts = LENGTH s.contexts
Proof
  strip_tac >>
  drule_at (Pat `_ _ = (_,_)`) psf_imp_length_contexts_preserved >> simp[]
QED

Theorem credited_abort_unuse_length[local]:
  s.contexts <> [] /\
  ignore_bind (credit_new_account charged) (abort_unuse gas) s = (r,t) ==>
  LENGTH t.contexts = LENGTH s.contexts
Proof
  strip_tac >>
  drule_at (Pat `_ _ = (_,_)`) psf_imp_length_contexts_preserved >> simp[]
QED

val peel_call_prefix_tac =
  dxrule_at (Pat `bind`) bind_call_prefix_grows_extract
  >> simp[call_prefix_leaves, create_prefix_charge_new_account]
  >> disch_then (qspec_then `s` mp_tac) >> simp[]
  >> strip_tac >> gvs[];

Theorem step_call_reaches_proceed_call:
  step_call op s = (r,s') /\ s.contexts <> [] /\
  LENGTH s.contexts < LENGTH s'.contexts ==>
  ?u sender address value ao az code gas mr.
    cp_rel s u /\ u.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys /\
    proceed_call op sender address value ao az code gas (Memory mr) u = (r,s') /\
    sender = (FST (HD s.contexts)).msgParams.callee /\
    value <= (lookup_account sender s.rollback.accounts).balance /\
    code = (case get_delegate (lookup_account address s.rollback.accounts).code of
      NONE => (lookup_account address s.rollback.accounts).code
    | SOME d => (lookup_account d s.rollback.accounts).code) /\
    (~call_has_value op ==> value = 0) /\
    (op = Call /\ 0 < value ==> ~(FST (HD s.contexts)).msgParams.static)
Proof
  simp[step_call_def] >> strip_tac
  >> `cp_rel s s /\ s.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys`
    by simp[call_prefix_refl]
  >> peel_call_prefix_tac >> pairarg_tac >> gvs[]
  >> qmatch_asmsub_abbrev_tac `proceed_call op _ address value ao az _ _ rd`
  >> peel_call_prefix_tac
  >> peel_call_prefix_tac
  >> `u''.rollback.accounts = s.rollback.accounts` by gvs[cp_rel_def]
  >> gvs[get_accounts_def, Once bind_def, return_def]
  >> drule_at (Pat `bind`) bind_call_prefix_grows_extract
  >> disch_then (qspec_then `s` mp_tac) >> simp[]
  >> (impl_tac >- irule call_prefix_delegate_code_selection)
  >> qpat_x_assum `bind _ _ _ = _` kall_tac
  >> strip_tac >> gvs[] >> pairarg_tac >> gvs[]
  >> `code = (case get_delegate (lookup_account address s.rollback.accounts).code of
       NONE => (lookup_account address s.rollback.accounts).code
     | SOME d => (lookup_account d s.rollback.accounts).code)`
    by (Cases_on `get_delegate (lookup_account address s.rollback.accounts).code`
        >> gvs[bind_def, return_def, AllCaseEqs()])
  >> gvs[ignore_bind_def] >> peel_call_prefix_tac
  >> qpat_x_assum `pop_stack _ _ = _` kall_tac
  >> qpat_x_assum `memory_expansion_info _ _ _ = _` kall_tac
  >> qpat_x_assum `access_address _ _ = _` kall_tac
  >> qpat_x_assum `(case _ of NONE => _ | SOME _ => _) _ = _` kall_tac
  >> peel_call_prefix_tac
  >> drule_at (Pat `bind`) bind_call_prefix_grows_extract
  >> simp[] >> disch_then (qspec_then `s` mp_tac) >> simp[]
  >> (impl_tac >- (Cases_on `op = Call /\ 0 < value` >> simp[call_prefix_leaves]))
  >> qpat_x_assum `bind _ _ _ = _` kall_tac
  >> strip_tac >> gvs[]
  >> `op = Call /\ 0 < value ==> ~(FST (HD s.contexts)).msgParams.static`
    by (strip_tac
        >> gvs[assert_not_static_def, get_static_def, get_current_context_def,
               bind_def, assert_def, return_def, fail_def, cp_rel_def, AllCaseEqs()])
  >> peel_call_prefix_tac
  >> peel_call_prefix_tac >> pairarg_tac >> gvs[]
  >> peel_call_prefix_tac
  >> peel_call_prefix_tac
  >> rename1 `get_callee beforeSender = (INL sender,afterSender)`
  >> `sender = (FST (HD s.contexts)).msgParams.callee`
    by gvs[get_callee_def, get_current_context_def, bind_def, return_def,
           fail_def, cp_rel_def, AllCaseEqs()]
  >> gvs[COND_RATOR]
  >> Cases_on `(lookup_account (FST (HD s.contexts)).msgParams.callee
                 s.rollback.accounts).balance < value` >> gvs[]
  >- (drule_at (Pat `_ = (_,s')`) psf_imp_length_contexts_preserved
      >> simp[] >> imp_res_tac call_prefix_contexts >> gvs[])
  >> peel_call_prefix_tac
  >> peel_call_prefix_tac >> gvs[COND_RATOR]
  >> rename1 `get_num_contexts depthState = (INL depth,entry)`
  >> Cases_on `depth > 1024` >> gvs[]
  >- (drule_at (Pat `_ = (_,s')`) psf_imp_length_contexts_preserved
      >> simp[] >> imp_res_tac call_prefix_contexts >> gvs[])
  >> qexistsl_tac [`entry`, `address`, `value`, `ao`, `az`, `stipend`]
  >> simp[] >> gvs[Abbr `rd`]
  >> qexists_tac `<|offset := w2n (EL ((if call_has_value op then 1 else 0) + 4) x);
                   size := w2n (EL ((if call_has_value op then 1 else 0) + 5) x)|>`
  >> simp[] >> simp[Abbr `value`]
QED

Theorem proceed_call_saved_rollback:
  proceed_call op sender address value ao az code gas rd s = (r, s') /\
  s.contexts <> [] /\ ~fIN address precompile_addresses ==>
  SND (HD s'.contexts) = s.rollback /\
  s'.rollback.accesses.storageKeys = s.rollback.accesses.storageKeys
Proof
  strip_tac >> Cases_on `op <> CallCode /\ 0 < value`
  >> gvs[proceed_call_def, bind_def, ignore_bind_def,
       get_accounts_def, drain_state_gas_reservoir_def, set_current_context_def,
       get_rollback_def, read_memory_def, get_current_context_def,
       get_caller_def, get_value_def, get_static_def,
       push_context_def, update_accounts_def, return_def, fail_def,
       AllCaseEqs()]
QED

Theorem terminal_bind:
  (!x s. ISR (FST (f x s))) ==> ISR (FST (bind g f s))
Proof
  rw[bind_def] >> Cases_on `g s` >> Cases_on `q` >> gvs[]
QED

Theorem terminal_ignore_bind:
  (!s. ISR (FST (f s))) ==> ISR (FST (ignore_bind g f s))
Proof
  simp[ignore_bind_def] >> strip_tac >> irule terminal_bind >> simp[]
QED

Theorem dispatch_precompiles_terminal:
  ISR (FST (dispatch_precompiles a s))
Proof
  rw[dispatch_precompiles_def]
  >> simp[precompile_ecrecover_def, precompile_sha2_256_def,
          precompile_ripemd_160_def, precompile_identity_def,
          precompile_modexp_def, precompile_ecadd_def,
          precompile_ecmul_def, precompile_ecpairing_def,
          precompile_blake2f_def, precompile_point_eval_def,
          precompile_bls_g1add_def, precompile_bls_g1msm_def,
          precompile_bls_g2add_def, precompile_bls_g2msm_def,
          precompile_bls_pairing_def, precompile_bls_map_fp_to_g1_def,
          precompile_bls_map_fp2_to_g2_def, precompile_p256verify_def,
          fail_def]
  >> rpt (FIRST [irule terminal_bind >> rpt gen_tac,
                 irule terminal_ignore_bind >> gen_tac,
                 CHANGED_TAC (simp[finish_def, fail_def]),
                 BasicProvers.PURE_CASE_TAC])
QED

Theorem proceed_call_inl_nonprecompile:
  proceed_call op sender address value ao az code gas rd s = (INL (), s') /\
  s.contexts <> [] ==> ~fIN address precompile_addresses
Proof
  strip_tac >> strip_tac
  >> Cases_on `op <> CallCode /\ 0 < value`
  >> gvs[proceed_call_def, bind_def, ignore_bind_def,
       get_accounts_def, drain_state_gas_reservoir_def, set_current_context_def,
       get_rollback_def, read_memory_def, get_current_context_def,
       get_caller_def, get_value_def, get_static_def,
       push_context_def, update_accounts_def, return_def, fail_def,
       AllCaseEqs()]
  >> qmatch_asmsub_abbrev_tac `dispatch_precompiles address pushed`
  >> `ISR (FST ((dispatch_precompiles address : unit execution) pushed))`
       by simp[dispatch_precompiles_terminal]
  >> qpat_x_assum `ISR _` mp_tac
  >> qpat_x_assum `dispatch_precompiles _ _ = _` (fn th => simp[th, sumTheory.ISR])
QED

Theorem proceed_call_saved_accounts:
  s.contexts <> [] /\
  proceed_call op sender address value argsOffset argsSize code stipend
    outputTo s = (r,t) ==>
  (SND (HD t.contexts)).accounts = s.rollback.accounts
Proof
  strip_tac >> qhdtm_x_assum `proceed_call` mp_tac >>
  simp[proceed_call_def, bind_def, ignore_bind_def, get_rollback_def,
       get_accounts_def, drain_state_gas_reservoir_def, set_current_context_def,
       read_memory_def, get_current_context_def, return_def] >>
  Cases_on `op <> CallCode /\ 0 < value` >>
  simp[update_accounts_def, return_def, get_caller_def, get_value_def,
       get_static_def, get_current_context_def, bind_def,
       push_context_def, ignore_bind_def] >>
  qmatch_goalsub_abbrev_tac `(if _ then _ else _) ss` >>
  qmatch_goalsub_abbrev_tac `m ss = _` >> strip_tac >>
  `ss.contexts <> []` by simp[Abbr `ss`] >>
  `cp m` by
    (simp[Abbr `m`] >>
     Cases_on `fIN address precompile_addresses` >> simp[]) >>
  `cp_rel ss t` by
    (qpat_x_assum `cp m` mp_tac >>
     rewrite_tac[cp_eq_preserves_when, preserves_when_def] >>
     disch_then drule >> simp[]) >>
  `SND (HD t.contexts) = SND (HD ss.contexts)` by
    gvs[cp_rel_def] >>
  simp[Abbr `ss`]
QED

Theorem step_call_grow_saved_accounts:
  s.contexts <> [] /\ step_call op s = (r,t) /\
  LENGTH s.contexts < LENGTH t.contexts ==>
  (SND (HD t.contexts)).accounts = s.rollback.accounts
Proof
  strip_tac >> drule_all step_call_reaches_proceed_call >> strip_tac >>
  `u.contexts <> []` by
    (gvs[cp_rel_def] >> Cases_on `s.contexts` >> gvs[]) >>
  drule_all proceed_call_saved_accounts >> gvs[cp_rel_def]
QED

Theorem step_create_saved_head_nonce_code:
  step_create two s = (INL (),t) /\ s.contexts <> [] /\
  LENGTH s.contexts < LENGTH t.contexts ==>
  (lookup_account a s.rollback.accounts).nonce <=
    (lookup_account a (SND (HD t.contexts)).accounts).nonce /\
  (lookup_account a (SND (HD t.contexts)).accounts).code =
    (lookup_account a s.rollback.accounts).code
Proof
  strip_tac >> drule_all step_create_reaches_proceed_create >> strip_tac >>
  drule_all call_prefix_contexts >> strip_tac >>
  drule_all proceed_create_frame_effects >> strip_tac >>
  gvs[cp_rel_def, increment_nonce_lookup, increment_nonce_code] >>
  Cases_on `a = (FST (HD s.contexts)).msgParams.callee` >> gvs[]
QED

Theorem step_growth_saved_head_nonce_code:
  wf_state s /\ step s = (r,t) /\ LENGTH s.contexts < LENGTH t.contexts ==>
  (lookup_account a s.rollback.accounts).nonce <=
    (lookup_account a (SND (HD t.contexts)).accounts).nonce /\
  (lookup_account a (SND (HD t.contexts)).accounts).code =
    (lookup_account a s.rollback.accounts).code
Proof
  strip_tac >> `s.contexts <> []` by gvs[wf_state_def] >>
  drule_all step_grow_dispatch >> strip_tac
  >- (drule_all step_call_grow_saved_accounts >> simp[]) >>
  drule_all step_create_saved_head_nonce_code >> simp[]
QED

Theorem proceed_call_memory_output:
  s.contexts <> [] /\
  proceed_call op sender address value ao az code stipend (Memory mr) s = (r,t) ==>
  (FST (HD t.contexts)).msgParams.outputTo = Memory mr
Proof
  Cases_on `s.contexts` >> simp[] >>
  simp[proceed_call_def, bind_def, ignore_bind_def,
       get_accounts_def, drain_state_gas_reservoir_def, set_current_context_def,
       get_rollback_def, read_memory_def, get_caller_def,
       get_value_def, get_static_def, update_accounts_def,
       push_context_def, get_current_context_def, return_def] >>
  Cases_on `op <> CallCode /\ 0 < value` >>
  Cases_on `fIN address precompile_addresses` >> simp[return_def] >>
  strip_tac >> gvs[update_accounts_def, get_current_context_def,
       return_def, initial_context_def, initial_msg_params_def] >>
  qmatch_asmsub_abbrev_tac `dispatch_precompiles address pushed` >>
  `pushed.contexts <> []` by simp[Abbr `pushed`] >>
  mp_tac (INST_TYPE [alpha |-> ``:unit``]
    (Q.INST [`a` |-> `address`] preserves_same_frame_dispatch_precompiles)) >>
  rewrite_tac[preserves_same_frame_def] >>
  disch_then drule >> simp[] >> strip_tac >>
  gvs[same_frame_rel_def, Abbr `pushed`, initial_context_def,
      initial_msg_params_def]
QED

Theorem step_growth_nonce_certificate:
  wf_state s /\ step s = (r,t) /\
  LENGTH s.contexts < LENGTH t.contexts /\
  (FST (HD t.contexts)).msgParams.outputTo = Code b ==>
  0 < (lookup_account b t.rollback.accounts).nonce
Proof
  strip_tac >> `s.contexts <> []` by gvs[wf_state_def] >>
  drule_all step_grow_dispatch >> strip_tac
  >- (drule_all step_call_reaches_proceed_call >> strip_tac >>
      drule_all call_prefix_contexts >> strip_tac >>
      drule_all proceed_call_memory_output >> simp[]) >>
  drule_all step_create_growth_effects >> strip_tac >> gvs[]
QED

Theorem set_last_accounts_foreign_lookup:
  ls <> [] /\ a <> address ==>
  MAP (\p. lookup_account a (SND p).accounts)
    (set_last_accounts (update_account address empty_account_state
      (SND (LAST ls)).accounts) ls) =
  MAP (\p. lookup_account a (SND p).accounts) ls
Proof
  Induct_on `ls` using SNOC_INDUCT >>
  simp[set_last_accounts_def, FRONT_SNOC, LAST_SNOC, MAP_SNOC,
       lookup_account_def, update_account_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem proceed_create_old_snapshot_lookups:
  s.contexts <> [] /\ a <> address /\
  proceed_create sender address value code gas s = (r,t) ==>
  MAP (\p. lookup_account a (SND p).accounts) (TL t.contexts) =
  MAP (\p. lookup_account a (SND p).accounts) s.contexts
Proof
  strip_tac >> qhdtm_x_assum `proceed_create` mp_tac >>
  simp[proceed_create_def, ignore_bind_def, bind_def,
       get_accounts_def, drain_state_gas_reservoir_def, set_current_context_def,
       get_current_context_def,
       update_accounts_def, get_rollback_def, get_original_def,
       set_original_def, push_context_def, return_def] >>
  strip_tac >> gvs[] >> simp[set_last_accounts_foreign_lookup] >>
  Cases_on `s.contexts` >> gvs[]
QED

Theorem proceed_call_old_snapshot_lookups:
  proceed_call op sender address value ao az code gas rd s = (r,t) /\
  s.contexts <> [] /\ ~fIN address precompile_addresses ==>
  MAP (\p. lookup_account a (SND p).accounts) (TL t.contexts) =
  MAP (\p. lookup_account a (SND p).accounts) s.contexts
Proof
  strip_tac >> Cases_on `op <> CallCode /\ 0 < value` >>
  gvs[proceed_call_def, bind_def, ignore_bind_def,
      get_accounts_def, drain_state_gas_reservoir_def, set_current_context_def,
      get_rollback_def, read_memory_def, get_current_context_def,
      get_caller_def, get_value_def, get_static_def,
      push_context_def, update_accounts_def, return_def, fail_def,
      AllCaseEqs()] >>
  Cases_on `s.contexts` >> gvs[]
QED

Theorem step_create_old_snapshot_lookups:
  step_create two s = (INL (),t) /\ s.contexts <> [] /\
  LENGTH s.contexts < LENGTH t.contexts /\
  ((lookup_account a s.rollback.accounts).nonce <> 0 \/
   ~NULL (lookup_account a s.rollback.accounts).code) ==>
  MAP (\p. lookup_account a (SND p).accounts) (TL t.contexts) =
  MAP (\p. lookup_account a (SND p).accounts) s.contexts
Proof
  strip_tac >> drule_all step_create_reaches_proceed_create >> strip_tac >>
  drule_all call_prefix_contexts >> strip_tac >>
  `a <> address` by (strip_tac >> gvs[cp_rel_def, account_already_created_def]) >>
  drule_all proceed_create_old_snapshot_lookups >>
  gvs[cp_rel_def] >> Cases_on `s.contexts` >> gvs[]
QED

Theorem step_call_old_snapshot_lookups:
  step_call op s = (INL (),t) /\ s.contexts <> [] /\
  LENGTH s.contexts < LENGTH t.contexts ==>
  MAP (\p. lookup_account a (SND p).accounts) (TL t.contexts) =
  MAP (\p. lookup_account a (SND p).accounts) s.contexts
Proof
  strip_tac >> drule_all step_call_reaches_proceed_call >> strip_tac >>
  drule_all call_prefix_contexts >> strip_tac >>
  drule_all proceed_call_inl_nonprecompile >> strip_tac >>
  drule_all proceed_call_old_snapshot_lookups >> gvs[cp_rel_def] >>
  Cases_on `s.contexts` >> gvs[]
QED

Theorem step_growth_old_snapshot_lookups:
  wf_state s /\ step s = (r,t) /\ LENGTH s.contexts < LENGTH t.contexts /\
  ((lookup_account a s.rollback.accounts).nonce <> 0 \/
   ~NULL (lookup_account a s.rollback.accounts).code) ==>
  MAP (\p. lookup_account a (SND p).accounts) (TL t.contexts) =
  MAP (\p. lookup_account a (SND p).accounts) s.contexts
Proof
  strip_tac >> `s.contexts <> []` by gvs[wf_state_def] >>
  drule_all step_grow_dispatch >> strip_tac >>
  metis_tac[step_call_old_snapshot_lookups, step_create_old_snapshot_lookups]
QED

Theorem step_growth_old_snapshot_lookup:
  wf_state s /\ step s = (r,t) /\ LENGTH s.contexts < LENGTH t.contexts /\
  ((lookup_account a s.rollback.accounts).nonce <> 0 \/
   ~NULL (lookup_account a s.rollback.accounts).code) /\ i < LENGTH s.contexts ==>
  lookup_account a (SND (EL (SUC i) t.contexts)).accounts =
  lookup_account a (SND (EL i s.contexts)).accounts
Proof
  strip_tac >>
  `MAP (\p. lookup_account a (SND p).accounts) (TL t.contexts) =
   MAP (\p. lookup_account a (SND p).accounts) s.contexts`
    by metis_tac[step_growth_old_snapshot_lookups] >>
  pop_assum (mp_tac o Q.AP_TERM `EL i`) >>
  simp[EL_MAP, EL]
QED

(* These are ML abbreviations only; the exported facts have inline predicates. *)
val collision_protected = ``\(B:rollback_state) (rb:rollback_state). !a.
  account_already_created (lookup_account a B.accounts) ==>
  account_already_created (lookup_account a rb.accounts)``;

Theorem step_growth_collision_protection:
  0 < d /\ d <= LENGTH s.contexts /\ wf_state s /\
  step s = (r,t) /\ LENGTH s.contexts < LENGTH t.contexts /\
  EVERY (^collision_protected B)
    (s.rollback :: MAP SND (TAKE (LENGTH s.contexts - d) s.contexts)) ==>
  EVERY (^collision_protected B)
    (t.rollback :: MAP SND (TAKE (LENGTH t.contexts - d) t.contexts))
Proof
  strip_tac >> fs[] >> conj_tac
  >- (rpt strip_tac >> drule_all step_growth_nonce_code >>
      disch_then (qspec_then `a` mp_tac) >>
      `account_already_created (lookup_account a s.rollback.accounts)` by metis_tac[] >>
      gvs[account_already_created_def] >> decide_tac) >>
  `s.contexts <> [] /\ outputTo_consistent_stack s` by gvs[wf_state_def] >>
  `LENGTH t.contexts = SUC (LENGTH s.contexts)` by
    (`LENGTH t.contexts > LENGTH s.contexts` by simp[] >>
     drule_all step_push_structure >> simp[ADD1]) >>
  simp[EVERY_EL, EL_MAP, LENGTH_TAKE_EQ] >> rpt strip_tac >>
  `account_already_created (lookup_account a s.rollback.accounts)` by metis_tac[] >>
  Cases_on `n`
  >- (simp[EL_TAKE] >> drule_all step_growth_saved_head_nonce_code >>
      disch_then (qspec_then `a` mp_tac) >>
      gvs[account_already_created_def] >> decide_tac) >>
  `n' < LENGTH s.contexts /\ n' < LENGTH s.contexts - d` by decide_tac >>
  `lookup_account a (SND (EL (SUC n') t.contexts)).accounts =
     lookup_account a (SND (EL n' s.contexts)).accounts` by
    (irule step_growth_old_snapshot_lookup >>
     simp[] >> gvs[account_already_created_def] >> metis_tac[]) >>
  gvs[EL_TAKE, EVERY_EL, EL_MAP, LENGTH_TAKE_EQ] >>
  metis_tac[EL_TAKE]
QED

Theorem step_growth_code_provenance:
  wf_state s /\ step s = (r,t) /\ LENGTH s.contexts < LENGTH t.contexts /\
  ^collision_protected B s.rollback ==>
  !a. (FST (HD t.contexts)).msgParams.outputTo = Code a ==>
    ~account_already_created (lookup_account a B.accounts)
Proof
  strip_tac >> `s.contexts <> []` by gvs[wf_state_def] >>
  drule_all step_grow_dispatch >> strip_tac
  >- (drule_all step_call_reaches_proceed_call >> strip_tac >>
      drule_all call_prefix_contexts >> strip_tac >>
      drule_all proceed_call_memory_output >> simp[]) >>
  drule_all step_create_growth_effects >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem step_growth_protected_frames:
  0 < d /\ d <= LENGTH s.contexts /\ wf_state s /\
  step s = (r,t) /\ LENGTH s.contexts < LENGTH t.contexts /\
  ^collision_protected B s.rollback /\
  EVERY (\mp. !a. mp.outputTo = Code a ==>
    ~account_already_created (lookup_account a B.accounts))
    (MAP (\p. (FST p).msgParams) (TAKE (LENGTH s.contexts-d) s.contexts)) ==>
  EVERY (\mp. !a. mp.outputTo = Code a ==>
    ~account_already_created (lookup_account a B.accounts))
    (MAP (\p. (FST p).msgParams) (TAKE (LENGTH t.contexts-d) t.contexts))
Proof
  strip_tac >>
  `!a. (FST (HD t.contexts)).msgParams.outputTo = Code a ==>
    ~account_already_created (lookup_account a B.accounts)` by
    (qx_gen_tac `a` >> disch_tac >> fs[] >>
     irule (SRULE [] step_growth_code_provenance) >>
     qexistsl_tac [`r`, `s`, `t`] >> simp[]) >>
  `s.contexts <> [] /\ outputTo_consistent_stack s /\
   LENGTH t.contexts > LENGTH s.contexts` by gvs[wf_state_def] >>
  drule_all step_push_structure >> strip_tac >>
  irule protected_frames_push_transport >>
  conj_tac >- simp[] >>
  simp[] >> qexists_tac `s` >> simp[ADD1]
QED

val step_inner = ``do
  context <- get_current_context;
  case FLOOKUP context.msgParams.parsed context.pc of
  | SOME op => ignore_bind (step_inst op) (inc_pc_or_jump op)
  | NONE => if LENGTH context.msgParams.code <= context.pc
            then step_inst Stop else step_inst Invalid
  od``;

Theorem step_inst_inc_pc_nonce_code:
  s.contexts <> [] /\
  ignore_bind (step_inst op) (inc_pc_or_jump op) s = (r,t) ==>
  ^nonce_code_rel a s t
Proof
  strip_tac >>
  Cases_on `step_inst op s` >> rename1 `step_inst op s = (q,u)` >>
  `^nonce_code_rel a s u` by metis_tac[step_inst_nonce_code] >>
  `u.contexts <> []` by metis_tac[step_inst_preserves_nonempty_contexts, SND] >>
  Cases_on `q`
  >- (rename1 `step_inst op s = (INL x,u)` >> Cases_on `x` >>
      `inc_pc_or_jump op u = (r,t)` by gvs[ignore_bind_def, bind_def] >>
      `preserves_when (\s. s.contexts <> []) (^nonce_code_rel a)
         (inc_pc_or_jump op)` by (irule cp_nonce_code >> simp[]) >>
      qpat_x_assum `preserves_when _ _ _` mp_tac >>
      simp[preserves_when_def] >> disch_then drule >>
      disch_then drule >> strip_tac >>
      gvs[] >> decide_tac) >>
  gvs[ignore_bind_def, bind_def]
QED

Theorem step_inner_nonce_code:
  s.contexts <> [] /\ ^step_inner s = (r,t) ==>
  ^nonce_code_rel a s t
Proof
  strip_tac >> qpat_x_assum `bind _ _ s = _` mp_tac >>
  simp[bind_def, get_current_context_def, return_def] >>
  Cases_on `FLOOKUP (FST (HD s.contexts)).msgParams.parsed
    (FST (HD s.contexts)).pc` >> simp[]
  >- (IF_CASES_TAC >> strip_tac >>
      irule (SRULE [] step_inst_nonce_code) >> metis_tac[]) >>
  strip_tac >> irule (SRULE [] step_inst_inc_pc_nonce_code) >> metis_tac[]
QED

Theorem handle_exception_inl_pops:
  s.contexts <> [] /\ handle_exception e s = (INL x,t) ==>
  LENGTH t.contexts + 1 = LENGTH s.contexts
Proof
  simp[handle_exception_decomp] >>
  qmatch_goalsub_abbrev_tac `bind prefix _` >>
  `cp prefix` by simp[Abbr `prefix`, cp_state_gas_meter, cp_bind, cp_ignore_bind] >>
  Cases_on `prefix s` >> rename1 `prefix s = (res,sp)` >>
  simp[bind_def] >> strip_tac >>
  `LENGTH sp.contexts = LENGTH s.contexts` by
    (drule_all cp_imp_length_contexts_preserved >> simp[]) >>
  Cases_on `res` >> gvs[] >>
  `sp.contexts <> []` by (Cases_on `sp.contexts` >> gvs[]) >>
  Cases_on `LENGTH sp.contexts <= 1`
  >- gvs[handle_ex_helper_def, bind_def, get_num_contexts_def,
         return_def, reraise_def] >>
  drule_all handle_ex_helper_length >> simp[]
QED

Theorem handle_step_inl_pops:
  s.contexts <> [] /\ handle_step e s = (INL x,t) ==>
  LENGTH t.contexts + 1 = LENGTH s.contexts
Proof
  strip_tac >> qhdtm_x_assum `handle_step` mp_tac >>
  simp[handle_step_def] >> IF_CASES_TAC
  >- simp[reraise_def] >>
  simp[handle_def] >>
  strip_assume_tac (INST_TYPE [alpha |-> ``:unit``] handle_create_INR) >>
  simp[] >> strip_tac >>
  drule_all handle_create_preserves_tl_and_snd_hd >> strip_tac >>
  drule_all handle_create_preserves_length >> strip_tac >>
  drule_all handle_exception_inl_pops >> simp[]
QED

Theorem handle_exception_length_one:
  LENGTH s.contexts = 1 /\ handle_exception e s = (r,t) ==>
  LENGTH t.contexts = 1
Proof
  metis_tac[handle_exception_preserves_length_1]
QED

Theorem handle_exception_rollback_sources:
  s.contexts <> [] /\ handle_exception e s = (r,t) ==>
  t.rollback = s.rollback \/
  (2 <= LENGTH s.contexts /\ t.rollback = SND (HD s.contexts))
Proof
  strip_tac >>
  Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- metis_tac[handle_exception_same_length_preserves_rollback] >>
  drule_all handle_exception_shrinks_by_one >> strip_tac >>
  `LENGTH t.contexts < LENGTH s.contexts` by decide_tac >>
  `2 <= LENGTH s.contexts` by
    (Cases_on `LENGTH s.contexts = 1`
     >- (drule_all handle_exception_length_one >> simp[]) >>
     Cases_on `s.contexts` >> gvs[] >> Cases_on `t'` >> gvs[]) >>
  Cases_on `s.contexts` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  PairCases_on `h` >>
  `LENGTH t.contexts < LENGTH s.contexts` by (gvs[] >> decide_tac) >>
  drule_at (Pat `s.contexts = _`) (cj 1 handle_exception_pop_generic_gen) >>
  simp[] >> disch_then irule >> simp[] >> gvs[] >> metis_tac[]
QED

Theorem handle_step_protected_account:
  s.contexts <> [] /\ handle_step e s = (r,t) /\
  ((lookup_account a s.rollback.accounts).nonce <> 0 \/
   ~NULL (lookup_account a s.rollback.accounts).code) /\
  (2 <= LENGTH s.contexts ==>
    (lookup_account a (SND (HD s.contexts)).accounts).nonce <> 0 \/
    ~NULL (lookup_account a (SND (HD s.contexts)).accounts).code) /\
  ((FST (HD s.contexts)).msgParams.outputTo = Code a ==>
    0 < (lookup_account a s.rollback.accounts).nonce) ==>
  (lookup_account a t.rollback.accounts).nonce <> 0 \/
    ~NULL (lookup_account a t.rollback.accounts).code
Proof
  strip_tac >> (
  qhdtm_x_assum `handle_step` mp_tac >>
  simp[handle_step_def] >> IF_CASES_TAC
  >- (simp[reraise_def] >> strip_tac >> gvs[]) >>
  simp[handle_def] >>
  strip_assume_tac (INST_TYPE [alpha |-> ``:unit``] handle_create_INR) >>
  simp[] >> strip_tac >>
  drule_all handle_create_preserves_tl_and_snd_hd >> strip_tac >>
  drule_all handle_create_preserves_length >> strip_tac >>
  `((lookup_account a s'.rollback.accounts).nonce <> 0 \/
    ~NULL (lookup_account a s'.rollback.accounts).code)` by
      (irule (INST_TYPE [alpha |-> ``:unit``] handle_create_protected_account) >>
       metis_tac[]) >>
  drule_all handle_exception_rollback_sources >> strip_tac >> gvs[])
QED

Theorem step_inner_inr_grow_protected_head:
  wf_state s /\ ^step_inner s = (INR e,u) /\
  LENGTH s.contexts < LENGTH u.contexts /\
  ((lookup_account a s.rollback.accounts).nonce <> 0 \/
   ~NULL (lookup_account a s.rollback.accounts).code) ==>
  (?mr. (FST (HD u.contexts)).msgParams.outputTo = Memory mr) /\
  ((lookup_account a (SND (HD u.contexts)).accounts).nonce <> 0 \/
   ~NULL (lookup_account a (SND (HD u.contexts)).accounts).code)
Proof
  strip_tac >> (
  `s.contexts <> [] /\ outputTo_consistent s` by
    metis_tac[wf_state_def, outputTo_consistent_stack_imp_consistent] >>
  gvs[bind_def, get_current_context_def, return_def, fail_def,
      COND_RATOR, vfmTypesTheory.option_CASE_rator, AllCaseEqs(),
      ignore_bind_def]
  >~ [`step_inst Stop`]
  >- (`preserves_same_frame (step_inst Stop)` by simp[] >>
      imp_res_tac psf_imp_length_contexts_preserved >> gvs[])
  >~ [`step_inst Invalid`]
  >- (`preserves_same_frame (step_inst Invalid)` by simp[] >>
      imp_res_tac psf_imp_length_contexts_preserved >> gvs[])
  >- (`preserves_same_frame (inc_pc_or_jump op)` by simp[] >>
      drule_then drule psf_imp_length_contexts_preserved >>
      (impl_tac >-
        (strip_tac >>
         gvs[inc_pc_or_jump_def, COND_RATOR, AllCaseEqs(), return_def] >>
         gvs[bind_def, AllCaseEqs(), get_current_context_def, fail_def])) >>
      strip_tac >> drule step_inst_inl_grew_is_call >> gvs[] >>
      strip_tac >> gvs[inc_pc_or_jump_def, return_def]) >>
  rename1 `step_inst op s = (INR e,u)` >>
  drule step_inst_inr_grew_is_call_family >>
  (impl_tac >- gvs[]) >>
  reverse (Cases_on `step_inst op s = step_call op s`)
  >- (strip_tac >> gvs[step_inst_def]) >>
  gvs[] >>
  `(SND (HD u.contexts)).accounts = s.rollback.accounts` by
    (irule step_call_grow_saved_accounts >> metis_tac[]) >>
  strip_tac >>
  drule step_call_inr_grow_structure >>
  disch_then (qspecl_then [`u`,`op`,`e`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[])
QED

Theorem step_continuing_collision_current:
  0 < d /\ d <= LENGTH s.contexts /\ wf_state s /\
  step s = (INL x,t) /\ d <= LENGTH t.contexts /\
  EVERY (^collision_protected B)
    (s.rollback :: MAP SND (TAKE (LENGTH s.contexts-d) s.contexts)) /\
  EVERY (\mp. !a. mp.outputTo = Code a ==>
    ~account_already_created (lookup_account a B.accounts))
    (MAP (\p. (FST p).msgParams) (TAKE (LENGTH s.contexts-d) s.contexts)) ==>
  ^collision_protected B t.rollback
Proof
  simp[] >> strip_tac >> qx_gen_tac `a` >> disch_tac >>
  `account_already_created (lookup_account a s.rollback.accounts)` by metis_tac[] >>
  `s.contexts <> []` by gvs[wf_state_def] >>
  qhdtm_x_assum `step` mp_tac >>
  simp[step_def, handle_def] >>
  Cases_on `^step_inner s` >> rename1 `^step_inner s = (q,u)` >>
  `^nonce_code_rel a s u` by
    (irule step_inner_nonce_code >> metis_tac[]) >>
  `same_frame_or_grow ^step_inner` by simp[] >>
  `LENGTH s.contexts <= LENGTH u.contexts` by
    (drule_all same_frame_or_grow_length >> simp[]) >>
  `u.contexts <> []` by (strip_tac >> gvs[]) >>
  `account_already_created (lookup_account a u.rollback.accounts)` by
    (gvs[account_already_created_def] >> decide_tac) >>
  Cases_on `q` >> simp[] >> strip_tac
  >- gvs[] >>
  rename1 `handle_step e u = (INL (),t)` >>
  Cases_on `LENGTH u.contexts = LENGTH s.contexts`
  >- (drule_all handle_step_inl_pops >> strip_tac >>
      `d < LENGTH s.contexts` by decide_tac >>
      `same_frame_rel s u` by
        (drule_all same_frame_or_grow_eq_length >> simp[]) >>
      `account_already_created (lookup_account a (SND (HD s.contexts)).accounts) /\
       (FST (HD s.contexts)).msgParams.outputTo <> Code a` by
        (Cases_on `s.contexts` >> gvs[] >> metis_tac[]) >>
      `(lookup_account a t.rollback.accounts).nonce <> 0 \/
       ~NULL (lookup_account a t.rollback.accounts).code`
        suffices_by simp[account_already_created_def] >>
      irule handle_step_protected_account >>
      qexistsl_tac [`e`, `INL ()`, `u`] >>
      gvs[same_frame_rel_def, account_already_created_def]) >>
  `LENGTH s.contexts < LENGTH u.contexts` by decide_tac >>
  `((lookup_account a s.rollback.accounts).nonce <> 0 \/
    ~NULL (lookup_account a s.rollback.accounts).code)` by
    gvs[account_already_created_def] >>
  drule_at (Pat `bind _ _ _ = _`) step_inner_inr_grow_protected_head >>
  disch_then (qspec_then `a` mp_tac) >> simp[] >> strip_tac >>
  `(lookup_account a t.rollback.accounts).nonce <> 0 \/
   ~NULL (lookup_account a t.rollback.accounts).code`
    suffices_by simp[account_already_created_def] >>
  irule handle_step_protected_account >>
  qexistsl_tac [`e`, `INL ()`, `u`] >>
  gvs[account_already_created_def]
QED

Theorem step_continuing_collision_protection:
  0 < d /\ d <= LENGTH s.contexts /\ wf_state s /\
  step s = (INL x,t) /\ d <= LENGTH t.contexts /\
  EVERY (^collision_protected B)
    (s.rollback :: MAP SND (TAKE (LENGTH s.contexts-d) s.contexts)) /\
  EVERY (\mp. !a. mp.outputTo = Code a ==>
    ~account_already_created (lookup_account a B.accounts))
    (MAP (\p. (FST p).msgParams) (TAKE (LENGTH s.contexts-d) s.contexts)) ==>
  EVERY (^collision_protected B)
    (t.rollback :: MAP SND (TAKE (LENGTH t.contexts-d) t.contexts))
Proof
  strip_tac >>
  `^collision_protected B t.rollback` by
    (irule step_continuing_collision_current >>
     qexistsl_tac [`d`, `s`, `x`] >> simp[]) >>
  `s.contexts <> [] /\ outputTo_consistent_stack s /\
   outputTo_consistent s /\ EVERY (wf_context o FST) s.contexts` by
    (gvs[wf_state_def] >> metis_tac[outputTo_consistent_stack_imp_consistent]) >>
  Cases_on `LENGTH s.contexts < LENGTH t.contexts`
  >- (irule step_growth_collision_protection >> simp[] >>
      qexistsl_tac [`INL x`, `s`] >> fs[]) >>
  Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (`same_frame_rel (zero_head_refunds s) t` by
        metis_tac[step_same_frame, zero_head_refunds_def] >>
      irule protected_rollbacks_same_frame_transport >> simp[] >>
      qexists_tac `zero_head_refunds s` >> simp[] >>
      Cases_on `s.contexts` >>
      gvs[zero_head_refunds_def] >>
      Cases_on `SUC (LENGTH t') - d` >> gvs[]) >>
  `LENGTH t.contexts < LENGTH s.contexts` by decide_tac >>
  drule_all step_pop_structure >> strip_tac >>
  irule protected_rollbacks_pop_transport >> simp[] >>
  qexistsl_tac [`HD s.contexts`, `parent`, `s`] >> fs[]
QED

Theorem step_continuing_protected_frames:
  0 < d /\ d <= LENGTH s.contexts /\ wf_state s /\
  step s = (INL x,t) /\ d <= LENGTH t.contexts /\
  EVERY (^collision_protected B)
    (s.rollback :: MAP SND (TAKE (LENGTH s.contexts-d) s.contexts)) /\
  EVERY (\mp. !a. mp.outputTo = Code a ==>
    ~account_already_created (lookup_account a B.accounts))
    (MAP (\p. (FST p).msgParams) (TAKE (LENGTH s.contexts-d) s.contexts)) ==>
  EVERY (\mp. !a. mp.outputTo = Code a ==>
    ~account_already_created (lookup_account a B.accounts))
    (MAP (\p. (FST p).msgParams) (TAKE (LENGTH t.contexts-d) t.contexts))
Proof
  strip_tac >>
  `s.contexts <> [] /\ outputTo_consistent_stack s /\
   outputTo_consistent s /\ EVERY (wf_context o FST) s.contexts` by
    (gvs[wf_state_def] >> metis_tac[outputTo_consistent_stack_imp_consistent]) >>
  Cases_on `LENGTH s.contexts < LENGTH t.contexts`
  >- (irule step_growth_protected_frames >> simp[] >>
      qexistsl_tac [`INL x`, `s`] >> fs[]) >>
  Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (`same_frame_rel (zero_head_refunds s) t` by
        metis_tac[step_same_frame, zero_head_refunds_def] >>
      irule protected_frames_same_frame_transport >>
      qexists_tac `zero_head_refunds s` >> simp[] >>
      Cases_on `s.contexts` >> gvs[zero_head_refunds_def] >>
      Cases_on `SUC (LENGTH t') - d` >> gvs[]) >>
  `LENGTH t.contexts < LENGTH s.contexts` by decide_tac >>
  drule_all step_pop_structure >> strip_tac >>
  irule protected_frames_pop_transport >> simp[] >>
  qexistsl_tac [`HD s.contexts`, `parent`, `s`] >> fs[]
QED

(* Single-step preservation of run_call_inv, by length-change cases. *)

Theorem run_call_inv_step:
  ∀es s s' q r.
    es.contexts ≠ [] ∧
    run_call_inv es q s ∧ ISL q ∧
    LENGTH es.contexts ≤ LENGTH s.contexts ∧
    step s = (r, s') ⇒
    run_call_inv es r s'
Proof
  rpt gen_tac >> strip_tac >>
  fs[run_call_inv_def] >>
  `0 < LENGTH es.contexts` by (Cases_on `es.contexts` >> gvs[]) >>
  `s.contexts <> [] /\ outputTo_consistent s` by
    metis_tac[wf_state_def, outputTo_consistent_stack_imp_consistent] >>
  `wf_state s'` by metis_tac[step_preserves_wf_state, SND] >>
  `s'.txParams = es.txParams` by
    metis_tac[vfmTxParamsTheory.step_preserves_txParams, SND] >>
  simp[run_call_inv_def] >>
  conj_tac >- gvs[wf_state_def] >>
  conj_tac >- suspend "storage" >>
  strip_tac >> Cases_on `r` >> gvs[] >>
  conj_tac
  >- (`EVERY (^collision_protected es.rollback)
        (s'.rollback :: MAP SND
          (TAKE (LENGTH s'.contexts - LENGTH es.contexts) s'.contexts))`
        suffices_by simp[] >>
      irule step_continuing_collision_protection >>
      simp[] >> qexists_tac `s` >> simp[]) >>
  irule step_continuing_protected_frames >>
  simp[] >> qexists_tac `s` >> simp[]
QED

Resume run_call_inv_step[storage]:
  qmatch_goalsub_abbrev_tac `EVERY P (active_rollbacks _ s')` >>
  `EVERY P (active_rollbacks (LENGTH es.contexts) s)` by fs[Abbr `P`] >>
  `P s.rollback` by gvs[active_rollbacks_def] >>
  Cases_on `LENGTH s'.contexts = LENGTH s.contexts`
  >- (`same_frame_rel (zero_head_refunds s) s'` by
        metis_tac[step_same_frame, zero_head_refunds_def] >>
      irule active_rollbacks_same_frame_transport >>
      reverse conj_tac
      >- (qexists_tac `zero_head_refunds s` >> simp[] >>
          Cases_on `s.contexts` >> gvs[zero_head_refunds_def, active_rollbacks_def] >>
          Cases_on `SUC (SUC (LENGTH t)) - MAX 2 (LENGTH es.contexts)` >> gvs[]) >>
      simp[Abbr `P`] >> rpt gen_tac >> disch_tac >>
      drule_all step_same_length_preserves_non_accessed_storage >> strip_tac >>
      `~fIN (SK a k) s.rollback.accesses.storageKeys` by
        (fs[same_frame_rel_def, zero_head_refunds_def,
            SUBSET_DEF, finite_setTheory.fIN_IN] >>
         metis_tac[]) >> fs[]) >>
  Cases_on `LENGTH s.contexts < LENGTH s'.contexts`
  >- suspend "push_storage" >>
  suspend "pop_storage"
QED

Resume run_call_inv_step[push_storage]:
  drule step_push_structure >> (impl_tac >- simp[]) >> strip_tac >>
  `P s'.rollback` by
    (simp[Abbr `P`] >> rpt gen_tac >> disch_tac >>
     irule storage_slots_compose >> simp[] >>
     qexists_tac `s.rollback` >> fs[] >>
     qx_gen_tac `address` >> qx_gen_tac `key` >> disch_tac >>
     qpat_x_assum `!a. _ \/ _` (qspec_then `address` strip_assume_tac) >>
     simp[lookup_storage_def, empty_storage_def]) >>
  irule active_rollbacks_push_transport >> simp[ADD1] >>
  qexistsl_tac [`P`,
    `\rb next. toSet rb.accesses.storageKeys SUBSET toSet next.accesses.storageKeys /\
       (!a. (lookup_account a next.accounts).storage =
            (lookup_account a rb.accounts).storage)`, `s`] >>
  simp[] >>
  map_every qx_gen_tac [`rb`, `next`] >> strip_tac >>
  fs[Abbr `P`] >> rpt gen_tac >> disch_tac >>
  `~fIN (SK a k) rb.accesses.storageKeys` by
    (fs[SUBSET_DEF, finite_setTheory.fIN_IN] >> metis_tac[]) >>
  fs[]
QED

Resume run_call_inv_step[pop_storage]:
  `LENGTH s'.contexts < LENGTH s.contexts` by decide_tac >>
  `EVERY (wf_context o FST) s.contexts` by gvs[wf_state_def] >>
  drule_all step_pop_structure >>
  disch_then (qx_choosel_then [`head`, `parent`, `rest`] strip_assume_tac) >>
  `2 <= LENGTH s.contexts` by
    (qpat_assum `s.contexts = _` (fn th => pure_once_rewrite_tac[th]) >> simp[]) >>
  `P (SND (HD s.contexts))` by
    (`MEM (SND (HD s.contexts)) (active_rollbacks (LENGTH es.contexts) s)` by
       (irule (cj 2 active_rollbacks_pop_sources) >> simp[]) >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `?source. P source /\
    toSet source.accesses.storageKeys SUBSET toSet s'.rollback.accesses.storageKeys /\
    (!a. (lookup_account a s'.rollback.accounts).storage =
         (lookup_account a source.accounts).storage)` by metis_tac[] >>
  `P s'.rollback` by
    (fs[Abbr `P`] >> rpt gen_tac >> disch_tac >>
     `~fIN (SK a k) source.accesses.storageKeys` by
       (fs[SUBSET_DEF, finite_setTheory.fIN_IN] >> metis_tac[]) >>
     fs[] >> metis_tac[]) >>
  irule active_rollbacks_pop_transport >>
  simp[] >> qexistsl_tac [`HD s.contexts`, `parent`, `s`] >> fs[]
QED

Finalise run_call_inv_step

(* -------------------------------------------------------------------------
 * Main run_call preservation theorem.
 * ------------------------------------------------------------------------- *)

Theorem run_call_preserves_inv:
  ∀es res es'.
    wf_state es ∧
    (FST(HD es.contexts)).jumpDest = NONE ∧
    EVERY (λrb. storage_slot_preserved rb es.rollback)
          (MAP SND (TAKE 2 es.contexts)) ∧
    run_call es = SOME (res, es') ⇒
    run_call_inv es res es'
Proof
  rpt strip_tac
  >> `es.contexts ≠ []` by fs[wf_state_def]
  >> gvs[run_call_def]
  >> `(λ p. run_call_inv es (FST p) (SND p)) (res, es')` suffices_by simp[]
  >> irule (MP_CANON OWHILE_INV_IND)
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> simp[run_call_inv_refl]
  >> rpt gen_tac
  >> pairarg_tac >> simp[]
  >> strip_tac
  >> Cases_on `step s''` >> simp[]
  >> `s''.contexts ≠ []` by (
       Cases_on `s''.contexts` >> gvs[]
       >> Cases_on `es.contexts` >> gvs[outputTo_consistent_stack_def])
  >> irule run_call_inv_step
  >> simp[]
  >> qexistsl_tac [`r''`, `s''`]
  >> simp[]
QED

(* A slot nobody accessed keeps its value, unless a CREATE cleared the
   storage of an address that had no nonce and no code (EELS
   process_create_message destroys the old storage). *)
Theorem run_call_preserves_storage_outside_accessed_slots:
  ∀es r es'.
    wf_state es ∧
    (FST(HD es.contexts)).jumpDest = NONE ∧
    EVERY (λrb. storage_slot_preserved rb es.rollback)
          (MAP SND (TAKE 2 es.contexts)) ∧
    run_call es = SOME (r, es') ⇒
    ∀a k. ¬fIN (SK a k) es'.rollback.accesses.storageKeys ⇒
        lookup_storage k (lookup_account a es'.rollback.accounts).storage =
        lookup_storage k (lookup_account a es.rollback.accounts).storage ∨
        lookup_storage k (lookup_account a es'.rollback.accounts).storage = 0w ∧
        ¬account_already_created (lookup_account a es.rollback.accounts)
Proof
  rpt strip_tac
  >> drule_all run_call_preserves_inv
  >> rw[run_call_inv_def, active_rollbacks_saved]
QED

Theorem run_call_preserves_txParams:
  ∀es r es'.
    wf_state es ∧
    (FST(HD es.contexts)).jumpDest = NONE ∧
    EVERY (λrb. storage_slot_preserved rb es.rollback)
          (MAP SND (TAKE 2 es.contexts)) ∧
    run_call es = SOME (r, es') ⇒
    es'.txParams = es.txParams
Proof
  rpt strip_tac
  >> drule_all run_call_preserves_inv
  >> rw[run_call_inv_def]
QED

(* Single-context entry corollary for the standard top-level transaction. *)

Theorem run_call_preserves_storage_outside_accessed_slots_single:
    outputTo_consistent_ctx ctx ∧
    wf_context ctx ∧
    wf_accounts es.rollback.accounts ∧
    ctx.jumpDest = NONE ∧
    es.contexts = [(ctx, es.rollback)] ∧
    run_call es = SOME (r, es') ⇒
    ∀a k. ¬fIN (SK a k) es'.rollback.accesses.storageKeys ⇒
        lookup_storage k (lookup_account a es'.rollback.accounts).storage =
        lookup_storage k (lookup_account a es.rollback.accounts).storage ∨
        lookup_storage k (lookup_account a es'.rollback.accounts).storage = 0w ∧
        ¬account_already_created (lookup_account a es.rollback.accounts)
Proof
  rpt strip_tac
  >> irule run_call_preserves_storage_outside_accessed_slots
  >> gvs[outputTo_consistent_stack_def]
  >> simp[storage_slot_preserved_def]
  >> gvs[wf_state_def, all_accounts_def]
  >> gs[stack_room_ok_def, gas_stack_ok_def, outputTo_consistent_stack_def]
QED

Theorem run_call_preserves_storage_outside_accessed_slots_initial:
    es.contexts =
      [(initial_context callee code static rd charged sg t, es.rollback)] ∧
    wf_accounts es.rollback.accounts ∧
    (∀a. rd = Code a ⇒ callee = a) ∧
    run_call es = SOME (r, es') ⇒
    ∀a k. ¬fIN (SK a k) es'.rollback.accesses.storageKeys ⇒
        lookup_storage k (lookup_account a es'.rollback.accounts).storage =
        lookup_storage k (lookup_account a es.rollback.accounts).storage ∨
        lookup_storage k (lookup_account a es'.rollback.accounts).storage = 0w ∧
        ¬account_already_created (lookup_account a es.rollback.accounts)
Proof
  rpt strip_tac
  >> irule run_call_preserves_storage_outside_accessed_slots_single
  >> gvs[]
  >> simp[outputTo_consistent_ctx_def, initial_msg_params_def]
QED

Theorem run_call_preserves_txParams_single:
  ∀es r es'.
    outputTo_consistent_ctx ctx ∧ wf_context ctx ∧
    wf_accounts es.rollback.accounts ∧
    ctx.jumpDest = NONE ∧
    es.contexts = [(ctx,es.rollback)] ∧
    run_call es = SOME (r, es') ⇒
    es'.txParams = es.txParams
Proof
  rpt strip_tac
  >> irule run_call_preserves_txParams
  >> gvs[storage_slot_preserved_def]
  >> gvs[outputTo_consistent_stack_def, wf_state_def, all_accounts_def]
  >> gs[gas_stack_ok_def, stack_room_ok_def]
QED

Theorem run_call_eq_run_single_context:
  LENGTH es.contexts = 1 ⇒
  run_call es = run es
Proof
  rw[run_call_def,run_def] >>
  simp[OWHILE_def] >>
  qho_match_abbrev_tac`COND (∃n. P1 n es) _ _ = COND (∃n. P2 n es) _ _` >>
  simp[] >>
  `∀n es. LENGTH es.contexts ≥ 1 ⇒ P1 n es = P2 n es` by (
    Induct >> simp[Abbr`P1`,Abbr`P2`] >>
    simp[FUNPOW_SUC] >> rpt strip_tac >> gvs[] >>
    first_x_assum drule >> pairarg_tac >> gvs[] >>
    pairarg_tac >> gvs[] >>
    qmatch_asmsub_rename_tac`step s1 = (_,s2)` >>
    qmatch_asmsub_rename_tac`_ (_,s0) = (_,s1)` >>
    `s0.contexts <> []` by (strip_tac >> gvs[]) >>
    `s1.contexts <> []` by (
      qmatch_asmsub_abbrev_tac`FUNPOW f m x` >>
      `(λp. (SND p).contexts ≠ []) (FUNPOW f m x)` suffices_by rw[] >>
      irule FUNPOW_invariant >> rw[Abbr`f`,Abbr`x`] >>
      irule step_preserves_nonempty_contexts >> rw[] ) >>
    `s2.contexts <> []` by (
      drule step_preserves_nonempty_contexts >> rw[] ) >>
    Cases_on`LENGTH s1.contexts` >> gvs[] >>
    Cases_on`LENGTH s2.contexts` >> gvs[] ) >>
  gvs[]
QED
