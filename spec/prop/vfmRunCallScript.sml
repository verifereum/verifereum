(* ==========================================================================
 * run_call storage preservation: slots not in final storageKeys are unchanged.
 * The invariant tracks txParams and rollback states reachable by revert.
 * ========================================================================== *)
Theory vfmRunCall
Ancestors
  combin pair option pred_set list rich_list sum
  arithmetic finite_map While vfmTypes vfmConstants
  vfmContext vfmState vfmExecution vfmExecutionProp
  vfmStoragePredicates vfmSameFrame vfmStaticCalls
  vfmDecreasesGas vfmStepLength vfmHandleStep vfmRunWithinFrame
  vfmHeadStack vfmHeadGas vfmJumpDest
Libs
  dep_rewrite BasicProvers

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
  cheat  (* SCAFFOLD *)
QED

Theorem active_rollbacks_set_original[simp]:
  active_rollbacks n (SND (set_original a s)) = active_rollbacks n s
Proof
  cheat  (* SCAFFOLD *)
QED

(* Per-context outputTo consistency, needed across pops. *)

Theorem outputTo_consistent_stack_imp_consistent:
  outputTo_consistent_stack s ⇒ outputTo_consistent s
Proof
  cheat  (* SCAFFOLD *)
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

Definition run_call_inv_def:
  run_call_inv es s ⇔
    s.txParams = es.txParams ∧
    outputTo_consistent_stack s ∧
    wf_state s ∧
    EVERY (λrb. storage_slot_preserved rb es.rollback)
          (active_rollbacks (LENGTH es.contexts) s)
End

(* -------------------------------------------------------------------------
 * Reflexivity.
 * ------------------------------------------------------------------------- *)

Theorem run_call_inv_refl:
  wf_state es ∧
  (FST (HD es.contexts)).jumpDest = NONE ∧
  EVERY (λrb. storage_slot_preserved rb es.rollback)
        (MAP SND (TAKE 2 es.contexts)) ⇒
  run_call_inv es es
Proof
  cheat  (* SCAFFOLD *)
QED

(* Single-step preservation of run_call_inv: split on same-frame/push/pop. *)


(* Same-frame step storage preservation outside final storageKeys. *)

(* Same-frame case: non-callee storage is unchanged by callee_local_changes;
 * callee storage can change only via SSTORE, which first access-lists the slot. *)



(* Pushed rollback storage: when CALL/CREATE pushes, the new head's saved
 * rollback has the old rollback's storage. *)

(* proceed_call captures s.rollback as the pushed rollback. *)
Theorem proceed_call_pushed_rb_storage:
  proceed_call op sender address value argsOffset argsSize code stipend
                outputTo s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  ∀a. (lookup_account a (SND (HD s'.contexts)).accounts).storage =
      (lookup_account a s.rollback.accounts).storage
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

(* proceed_call push structure. *)
Theorem proceed_call_push_structure:
  proceed_call op sender address value argsOffset argsSize code stipend
               outputTo s = (r, s') ∧ s.contexts ≠ [] ⇒
  TL s'.contexts = s.contexts ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet s'.rollback.accesses.storageKeys ∧
  (FST (HD s'.contexts)).msgParams.outputTo = outputTo ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet (SND (HD s'.contexts)).accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

(* proceed_create push structure. *)
Theorem proceed_create_push_structure:
  proceed_create senderAddress address value code cappedGas s = (r, s') ∧
  s.contexts ≠ [] ⇒
  MAP FST (TL s'.contexts) = MAP FST s.contexts ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet s'.rollback.accesses.storageKeys ∧
  outputTo_consistent_ctx (FST (HD s'.contexts)) ∧
  toSet s.rollback.accesses.storageKeys ⊆ toSet (SND (HD s'.contexts)).accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

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
  cheat  (* SCAFFOLD *)
QED

(* bind composition for pushed-rb storage. *)
Theorem preserves_pushed_rb_storage_bind:
  preserves_storage g ∧ preserves_same_frame g ∧
  (∀x. preserves_pushed_rb_storage (f x)) ⇒
  preserves_pushed_rb_storage (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_pushed_rb_storage_ignore_bind:
  preserves_storage g ∧ preserves_same_frame g ∧
  preserves_pushed_rb_storage f ⇒
  preserves_pushed_rb_storage (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_pushed_rb_storage_cond[simp]:
  preserves_pushed_rb_storage m1 ∧ preserves_pushed_rb_storage m2 ⇒
  preserves_pushed_rb_storage (if b then m1 else m2)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Base case: proceed_call preserves pushed rb storage. *)
Theorem preserves_pushed_rb_storage_proceed_call[simp]:
  preserves_pushed_rb_storage
    (proceed_call op sender address value argsOffset argsSize
                  code stipend outputTo)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_pushed_rb_storage_proceed_create[simp]:
  preserves_pushed_rb_storage
    (proceed_create senderAddress address value code cappedGas)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Now step_call = a bunch of preserves_storage+preserves_same_frame
   primitives followed by either abort_call_value (which is
   preserves_same_frame, vacuously preserves_pushed_rb_storage),
   abort_unuse (likewise), or proceed_call. *)
Theorem preserves_pushed_rb_storage_step_call[simp]:
  preserves_pushed_rb_storage (step_call op)
Proof
  cheat  (* SCAFFOLD *)
QED

(* abort_create_exists doesn't grow contexts, so vacuously preserves
   pushed-rb storage. Unlike abort_call_value/abort_unuse, it is NOT
   unconditionally preserves_same_frame (it requires the sender address
   to match the current callee), so we prove it from the length lemma. *)
Theorem preserves_pushed_rb_storage_abort_create_exists[simp]:
  preserves_pushed_rb_storage (abort_create_exists a)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_pushed_rb_storage_step_create[simp]:
  preserves_pushed_rb_storage (step_create two)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Final user-facing lemmas. *)
Theorem step_call_pushed_rb_storage:
  ∀op s r s'. step_call op s = (r, s') ∧ s.contexts ≠ [] ∧
    LENGTH s'.contexts > LENGTH s.contexts ⇒
    ∀a. (lookup_account a (SND (HD s'.contexts)).accounts).storage =
        (lookup_account a s.rollback.accounts).storage
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_create_pushed_rb_storage:
  ∀two s r s'. step_create two s = (r, s') ∧ s.contexts ≠ [] ∧
    LENGTH s'.contexts > LENGTH s.contexts ⇒
    ∀a. (lookup_account a (SND (HD s'.contexts)).accounts).storage =
        (lookup_account a s.rollback.accounts).storage
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

(* TODO: move *)
Theorem LAST_CONS_SNOC:
  LAST (x::(SNOC y z)) = y
Proof
  cheat  (* SCAFFOLD *)
QED

(* TODO: move *)
Theorem FRONT_CONS_SNOC:
  FRONT (x::(SNOC y z)) = x::z
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

(* Full step storage preservation in the same-frame case. *)
Theorem step_preserves_non_accessed_storage:
  ∀s r s'. step s = (r, s') ∧ s.contexts ≠ [] ∧
    outputTo_consistent s ∧
    same_frame_rel s s' ⇒
  ∀a k. ¬fIN (SK a k) s'.rollback.accesses.storageKeys ⇒
    lookup_storage k (lookup_account a s'.rollback.accounts).storage =
    lookup_storage k (lookup_account a s.rollback.accounts).storage
Proof
  cheat  (* SCAFFOLD *)
QED

(* -------------------------------------------------------------------------
 * Stack room for CALL/CREATE growth.
 * ------------------------------------------------------------------------- *)

Theorem step_call_grow_parent_stack_room:
  wf_context (FST (HD s.contexts)) ∧ step_call op s = (r, s') ∧
  s.contexts ≠ [] ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
    LENGTH (FST (HD (TL s'.contexts))).stack < stack_limit
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_create_grow_parent_stack_room:
  wf_context (FST (HD s.contexts)) ∧ step_create two s = (r, s') ∧
  s.contexts ≠ [] ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
    LENGTH (FST (HD (TL s'.contexts))).stack < stack_limit
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_grow_parent_gas_monotone:
  step_call op s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
    (FST (HD s.contexts)).gasUsed ≤ (FST (EL 1 s'.contexts)).gasUsed
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_create_grow_parent_gas_monotone:
  step_create two s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
    (FST (HD s.contexts)).gasUsed ≤ (FST (EL 1 s'.contexts)).gasUsed
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem call_gas_stipend_le_consumed:
  (if 0 < value then call_stipend else 0) ≤ otherCost + memoryCost ∧
  call_gas value gas gasLeft memoryCost otherCost = (dynamicGas, stipend) ⇒
  stipend ≤ dynamicGas + memoryCost
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

Theorem step_create_grow_parent_gas_ok:
  wf_state s ∧ step_create two s = (r, s') ∧
  s.contexts ≠ [] ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
    (FST (HD s.contexts)).gasUsed +
    ((FST (HD s'.contexts)).msgParams.gasLimit -
     (FST (HD s'.contexts)).gasUsed) ≤
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  cheat  (* SCAFFOLD *)
QED

(* Named facts about the pre-handler inner step. *)

(* Full-step push structure: storage/access shape plus parent stack/gas facts. *)
Theorem step_push_structure:
  ∀s r s'. step s = (r, s') ∧ s.contexts ≠ [] ∧
    outputTo_consistent_stack s ∧ wf_state s ∧
    LENGTH s'.contexts > LENGTH s.contexts ⇒
    LENGTH s'.contexts = LENGTH s.contexts + 1 ∧
    (* Storage preservation for s'.rollback *)
    (∀a. (lookup_account a s'.rollback.accounts).storage =
         (lookup_account a s.rollback.accounts).storage) ∧
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
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

(* Full-step pop structure.  Rollback equality is weakened to storage equality
 * plus the matching accesses subset, because handle_create may change code. *)
Theorem step_inst_same_frame_gas_monotone:
   step_inst op s = (q, s') ∧
   same_frame_rel s s' ∧
   EVERY (wf_context o FST) s.contexts
   ⇒
     (FST (HD s.contexts)).gasUsed ≤
     (FST (HD s'.contexts)).gasUsed
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_pop_structure:
  ∀s r s'. step s = (r, s') ∧ s.contexts ≠ [] ∧
    outputTo_consistent_stack s ∧
    EVERY (wf_context o FST) s.contexts ∧
    LENGTH s'.contexts < LENGTH s.contexts ⇒
    ∃new_head parent rest.
      s.contexts = HD s.contexts :: parent :: rest ∧
      s'.contexts = (new_head, SND parent) :: rest ∧
      new_head.msgParams = (FST parent).msgParams ∧
      new_head.gasUsed ≥
        (FST parent).gasUsed -
        ((FST (HD s.contexts)).msgParams.gasLimit -
         (FST (HD s.contexts)).gasUsed) ∧
      ((toSet s.rollback.accesses.storageKeys ⊆
          toSet s'.rollback.accesses.storageKeys ∧
        (∀a. (lookup_account a s'.rollback.accounts).storage =
             (lookup_account a s.rollback.accounts).storage)) ∨
       (toSet (SND (HD s.contexts)).accesses.storageKeys ⊆
          toSet s'.rollback.accesses.storageKeys ∧
        (∀a. (lookup_account a s'.rollback.accounts).storage =
             (lookup_account a (SND (HD s.contexts)).accounts).storage)))
Proof
  cheat  (* SCAFFOLD *)
QED

(* -------------------------------------------------------------------------
 * Full wf_state preservation. Placed here because the strong wf_state
 * invariants use whole-step push/pop structure proved above.
 * ------------------------------------------------------------------------- *)

Theorem step_push_parent_stack_room:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s'.contexts > LENGTH s.contexts
  ⇒ LENGTH (FST (EL 1 s'.contexts)).stack < stack_limit
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_preserves_stack_room_ok:
  wf_state s ⇒ stack_room_ok (SND (step s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem same_frame_rel_preserves_outputTo_consistent_stack:
  same_frame_rel s s' ∧ outputTo_consistent_stack s ⇒
  outputTo_consistent_stack s'
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_preserves_outputTo_consistent_stack:
  wf_state s ⇒ outputTo_consistent_stack (SND (step s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_push_parent_gas_ok:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s'.contexts > LENGTH s.contexts ⇒
    (FST (HD s.contexts)).gasUsed +
    ((FST (HD s'.contexts)).msgParams.gasLimit -
     (FST (HD s'.contexts)).gasUsed) ≤
    (FST (EL 1 s'.contexts)).gasUsed
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inner_same_frame_gas_monotone:
  step_inner s = (r, s') ∧ same_frame_rel s s' ∧
  EVERY (wf_context o FST) s.contexts ⇒
    (FST (HD s.contexts)).gasUsed ≤
    (FST (HD s'.contexts)).gasUsed
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inner_push_preserves_stack_room_ok:
  wf_state s ∧ step_inner s = (r, s') ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
    stack_room_ok s'
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inner_push_preserves_gas_stack_ok:
  wf_state s ∧ step_inner s = (r, s') ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
    gas_stack_ok s'
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inner_preserves_stack_room_gas_ok:
  wf_state s ∧ step_inner s = (r, s') ⇒
    stack_room_ok s' ∧ gas_stack_ok s'
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_pop_preserves_gas_stack_ok:
  wf_state s ∧ step s = (r, s') ∧ LENGTH s'.contexts < LENGTH s.contexts ⇒
  gas_stack_ok s'
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_preserves_gas_stack_ok:
  wf_state s ⇒ gas_stack_ok (SND (step s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_preserves_wf_state:
  wf_state s ⇒ wf_state (SND (step s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_preserves_wf_state:
  wf_state s ∧ run s = SOME (r, s') ⇒ wf_state s'
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_call_preserves_wf_state:
  wf_state es ∧ run_call es = SOME (r, es') ⇒ wf_state es'
Proof
  cheat  (* SCAFFOLD *)
QED

(* Single-step preservation of run_call_inv, by length-change cases. *)

Theorem run_call_inv_step:
  ∀es s s' r.
    es.contexts ≠ [] ∧
    run_call_inv es s ∧
    LENGTH s.contexts ≥ LENGTH es.contexts ∧
    step s = (r, s') ⇒
    run_call_inv es s'
Proof
  cheat  (* SCAFFOLD *)
QED

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
    run_call_inv es es'
Proof
  cheat  (* SCAFFOLD *)
QED

(* Headline corollary: untouched storageKeys imply unchanged storage slot. *)

Theorem run_call_preserves_storage_outside_accessed_slots:
  ∀es r es'.
    wf_state es ∧
    (FST(HD es.contexts)).jumpDest = NONE ∧
    EVERY (λrb. storage_slot_preserved rb es.rollback)
          (MAP SND (TAKE 2 es.contexts)) ∧
    run_call es = SOME (r, es') ⇒
    ∀a k. ¬fIN (SK a k) es'.rollback.accesses.storageKeys ⇒
        lookup_storage k (lookup_account a es'.rollback.accounts).storage =
        lookup_storage k (lookup_account a es.rollback.accounts).storage
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
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
        lookup_storage k (lookup_account a es.rollback.accounts).storage
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_call_preserves_storage_outside_accessed_slots_initial:
    es.contexts = [(initial_context callee code static rd sg t, es.rollback)] ∧
    wf_accounts es.rollback.accounts ∧
    (∀a. rd = Code a ⇒ callee = a) ∧
    run_call es = SOME (r, es') ⇒
    ∀a k. ¬fIN (SK a k) es'.rollback.accesses.storageKeys ⇒
        lookup_storage k (lookup_account a es'.rollback.accounts).storage =
        lookup_storage k (lookup_account a es.rollback.accounts).storage
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

Theorem run_call_eq_run_single_context:
  LENGTH es.contexts = 1 ⇒
  run_call es = run es
Proof
  cheat  (* SCAFFOLD *)
QED
