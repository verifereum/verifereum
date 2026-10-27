Theory vfmAccountDeletion
Ancestors
  combin pair option list rich_list relation arithmetic While
  vfmTypes vfmState vfmContext vfmExecution vfmExecutionProp
  vfmSameFrame vfmRunWithinFrame vfmRunCall vfmStaticCalls vfmDecreasesGas
  vfmStoragePredicates vfmPreserves vfmHandleStep vfmStepLength
  vfmAccountFrame
Libs
  BasicProvers

(* -------------------------------------------------------------------------
 * Deletions.  SELFDESTRUCT schedules its callee for deletion only if the
 * callee is empty in the original accounts (originalAccounts), which only
 * a CREATE at that address changes.  A CREATE needs the address
 * not yet created, which an account with a nonce or code never becomes
 * again within run_call.
 * ------------------------------------------------------------------------- *)

(* Primitive projection boundaries for deletion provenance. *)
Theorem add_to_delete_membership:
  add_to_delete b s = (r, s') ⇒
  (MEM a s'.rollback.toDelete ⇔ a = b ∨ MEM a s.rollback.toDelete)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem get_original_accounts:
  s.contexts ≠ [] ⇒
  get_original s = (INL s.originalAccounts, s)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem set_last_accounts_projections:
  ls ≠ [] ⇒
  MAP FST (set_last_accounts ac ls) = MAP FST ls ∧
  MAP (λp. (SND p).toDelete) (set_last_accounts ac ls) =
    MAP (λp. (SND p).toDelete) ls ∧
  (SND (LAST (set_last_accounts ac ls))).accounts = ac
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem set_original_projections:
  s.contexts ≠ [] ∧ set_original ac s = (r, s') ⇒
  s'.rollback = s.rollback ∧
  s'.contexts = s.contexts ∧
  MAP FST s'.contexts = MAP FST s.contexts ∧
  MAP (λp. (SND p).toDelete) s'.contexts =
    MAP (λp. (SND p).toDelete) s.contexts ∧
  s'.originalAccounts = ac
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_deletion_original_projections:
  cp m ∧ s.contexts ≠ [] ∧ m s = (r, s') ⇒
  s'.rollback.toDelete = s.rollback.toDelete ∧
  MAP SND s'.contexts = MAP SND s.contexts ∧
  s'.originalAccounts =
    s.originalAccounts
Proof
  cheat  (* SCAFFOLD *)
QED

(* ML-only quotations, not new semantic definitions. *)
val deletion_exact = ``λ(s:execution_state) (t:execution_state).
  t.contexts ≠ [] ∧
  MAP (λp. (SND p).toDelete) t.contexts =
    MAP (λp. (SND p).toDelete) s.contexts ∧
  t.originalAccounts = s.originalAccounts ∧
  t.rollback.toDelete = s.rollback.toDelete``;

val deletion_rel = ``λa (s:execution_state) (t:execution_state).
  t.contexts ≠ [] ∧
  MAP (λp. (SND p).toDelete) t.contexts =
    MAP (λp. (SND p).toDelete) s.contexts ∧
  lookup_account a t.originalAccounts =
    lookup_account a s.originalAccounts ∧
  (MEM a t.rollback.toDelete ⇒ MEM a s.rollback.toDelete ∨
    account_empty (lookup_account a s.originalAccounts))``;

Theorem deletion_exact_refl:
  s.contexts ≠ [] ⇒ ^deletion_exact s s
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_exact_trans:
  ^deletion_exact s t ∧ ^deletion_exact t u ⇒ ^deletion_exact s u
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_rel_refl:
  s.contexts ≠ [] ⇒ ^deletion_rel a s s
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_rel_trans:
  ^deletion_rel a s t ∧ ^deletion_rel a t u ⇒ ^deletion_rel a s u
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_exact_imp_rel:
  ^deletion_exact s t ⇒ ^deletion_rel a s t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_exact_nonempty:
  ^deletion_exact s t ⇒ t.contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_rel_nonempty:
  ^deletion_rel a s t ⇒ t.contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_deletion_exact:
  cp m ⇒ preserves_when (λs. s.contexts ≠ []) ^deletion_exact m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem update_accounts_deletion_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact (update_accounts f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_deletion_exact_imp_rel:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact m ⇒
  preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_exact_bind:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact g ∧
  (∀x. preserves_when (λs. s.contexts ≠ []) ^deletion_exact (f x)) ⇒
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_rel_bind:
  preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) g ∧
  (∀x. preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) (f x)) ⇒
  preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_rel_ignore_bind:
  preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) g ∧
  preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) f ⇒
  preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_rel_bind_get_original:
  (∀s r t. s.contexts ≠ [] ∧
    f (s.originalAccounts) s = (r,t) ⇒
    ^deletion_rel a s t) ⇒
  preserves_when (λs. s.contexts ≠ []) (^deletion_rel a)
    (bind get_original f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_rel_bind_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact g ∧
  (∀x. preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) (f x)) ⇒
  preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_rel_ignore_bind_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact g ∧
  preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) f ⇒
  preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem push_logs_deletion_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact (push_logs logs)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_self_destruct_deletion_rel:
  preserves_when (λs. s.contexts ≠ []) (^deletion_rel a) step_self_destruct
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_exact_ignore_bind:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact g ∧
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact f ⇒
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem write_storage_deletion_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact (write_storage a k v)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem write_transient_storage_deletion_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact
    (write_transient_storage a k v)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_sstore_deletion_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact (step_sstore transient)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_log_deletion_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact (step_log n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inst_deletion_exact:
  op ≠ SelfDestruct ∧ op ≠ Create ∧ op ≠ Create2 ∧
  op ≠ Call ∧ op ≠ CallCode ∧ op ≠ DelegateCall ∧ op ≠ StaticCall ⇒
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact (step_inst op)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inc_pc_or_jump_deletion_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact (inc_pc_or_jump op)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_self_destruct_deletion_provenance:
  s.contexts ≠ [] ∧ step_self_destruct s = (r,t) ⇒
  MAP (λp. (SND p).toDelete) t.contexts =
    MAP (λp. (SND p).toDelete) s.contexts ∧
  lookup_account a t.originalAccounts =
    lookup_account a s.originalAccounts ∧
  (MEM a t.rollback.toDelete ⇒ MEM a s.rollback.toDelete ∨
    account_empty (lookup_account a s.originalAccounts))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem set_last_accounts_length:
  ls ≠ [] ⇒ LENGTH (set_last_accounts ac ls) = LENGTH ls
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_create_deletion_projections:
  s.contexts ≠ [] ∧
  proceed_create sender address value code gas s = (r,t) ⇒
  t.rollback.toDelete = s.rollback.toDelete ∧
  MAP (λp. (SND p).toDelete) t.contexts =
    s.rollback.toDelete :: MAP (λp. (SND p).toDelete) s.contexts ∧
  LENGTH t.contexts = SUC (LENGTH s.contexts) ∧
  t.originalAccounts =
    update_account address empty_account_state
      s.originalAccounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_call_deletion_projections:
  s.contexts ≠ [] ∧
  proceed_call op sender address value argsOffset argsSize code stipend
    outputTo s = (r,t) ⇒
  t.rollback.toDelete = s.rollback.toDelete ∧
  MAP (λp. (SND p).toDelete) t.contexts =
    s.rollback.toDelete :: MAP (λp. (SND p).toDelete) s.contexts ∧
  LENGTH t.contexts = SUC (LENGTH s.contexts) ∧
  t.originalAccounts = s.originalAccounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_call_saved_accounts:
  s.contexts ≠ [] ∧
  proceed_call op sender address value argsOffset argsSize code stipend
    outputTo s = (r,t) ⇒
  (SND (HD t.contexts)).accounts = s.rollback.accounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_grow_saved_accounts:
  s.contexts ≠ [] ∧ step_call op s = (r,t) ∧
  LENGTH s.contexts < LENGTH t.contexts ⇒
  (SND (HD t.contexts)).accounts = s.rollback.accounts
Proof
  cheat  (* SCAFFOLD *)
QED

val deletion_call = ``λ(s:execution_state) (t:execution_state).
  t.contexts ≠ [] ∧
  t.rollback.toDelete = s.rollback.toDelete ∧
  t.originalAccounts = s.originalAccounts ∧
  (MAP (λp. (SND p).toDelete) t.contexts =
     MAP (λp. (SND p).toDelete) s.contexts ∨
   MAP (λp. (SND p).toDelete) t.contexts =
     s.rollback.toDelete :: MAP (λp. (SND p).toDelete) s.contexts)``;

Theorem deletion_call_bind_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact g ∧
  (∀x. preserves_when (λs. s.contexts ≠ []) ^deletion_call (f x)) ⇒
  preserves_when (λs. s.contexts ≠ []) ^deletion_call (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_deletion_call:
  cp m ⇒ preserves_when (λs. s.contexts ≠ []) ^deletion_call m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_call_deletion_call:
  preserves_when (λs. s.contexts ≠ []) ^deletion_call
    (proceed_call op sender address value argsOffset argsSize code stipend outputTo)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_call_ignore_bind_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact g ∧
  preserves_when (λs. s.contexts ≠ []) ^deletion_call f ⇒
  preserves_when (λs. s.contexts ≠ []) ^deletion_call (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_deletion_call:
  preserves_when (λs. s.contexts ≠ []) ^deletion_call (step_call op)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_deletion_projections:
  s.contexts ≠ [] ∧ step_call op s = (r,t) ⇒
  t.rollback.toDelete = s.rollback.toDelete ∧
  t.originalAccounts = s.originalAccounts ∧
  ((MAP (λp. (SND p).toDelete) t.contexts =
      MAP (λp. (SND p).toDelete) s.contexts ∧
    LENGTH t.contexts = LENGTH s.contexts) ∨
   (MAP (λp. (SND p).toDelete) t.contexts =
      s.rollback.toDelete :: MAP (λp. (SND p).toDelete) s.contexts ∧
    LENGTH t.contexts = SUC (LENGTH s.contexts)))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem fixed_accounts_bind_cp:
  cp g ∧
  (∀x. preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A)
    R (f x)) ∧
  (∀s t. s.contexts ≠ [] ∧ cp_rel s t ⇒ R s t) ∧
  (∀s t u. s.contexts ≠ [] ∧ cp_rel s t ∧ R t u ⇒ R s u) ⇒
  preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A)
    R (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem fixed_accounts_ignore_bind_cp:
  cp g ∧
  preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A) R f ∧
  (∀s t. s.contexts ≠ [] ∧ cp_rel s t ⇒ R s t) ∧
  (∀s t u. s.contexts ≠ [] ∧ cp_rel s t ∧ R t u ⇒ R s u) ⇒
  preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A)
    R (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem fixed_accounts_bind_get_accounts:
  (∀A. preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A)
    (R A) (f A)) ⇒
  preserves_when (λs. s.contexts ≠ [])
    (λs t. R s.rollback.accounts s t) (bind get_accounts f)
Proof
  cheat  (* SCAFFOLD *)
QED

val deletion_create = ``λA (s:execution_state) (t:execution_state).
  t.contexts ≠ [] ∧ t.rollback.toDelete = s.rollback.toDelete ∧
  ((MAP (λp. (SND p).toDelete) t.contexts =
      MAP (λp. (SND p).toDelete) s.contexts ∧
    LENGTH t.contexts = LENGTH s.contexts ∧
    t.originalAccounts = s.originalAccounts) ∨
   (∃b. MAP (λp. (SND p).toDelete) t.contexts =
          s.rollback.toDelete :: MAP (λp. (SND p).toDelete) s.contexts ∧
        LENGTH t.contexts = SUC (LENGTH s.contexts) ∧
        t.originalAccounts =
          update_account b empty_account_state s.originalAccounts ∧
        (lookup_account b A).nonce = 0 ∧ NULL (lookup_account b A).code))``;

Theorem cp_rel_deletion_exact:
  s.contexts ≠ [] ∧ cp_rel s t ⇒ ^deletion_exact s t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_exact_imp_create:
  ^deletion_exact s t ⇒ ^deletion_create A s t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_create_transport:
  ^deletion_exact s t ∧ ^deletion_create A t u ⇒ ^deletion_create A s u
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_rel_deletion_create:
  s.contexts ≠ [] ∧ cp_rel s t ⇒ ^deletion_create A s t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_rel_deletion_create_transport:
  s.contexts ≠ [] ∧ cp_rel s t ∧ ^deletion_create A t u ⇒
  ^deletion_create A s u
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_create_bind_cp:
  cp g ∧
  (∀x. preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A)
    (^deletion_create A) (f x)) ⇒
  preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A)
    (^deletion_create A) (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_create_ignore_bind_cp:
  cp g ∧
  preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A)
    (^deletion_create A) f ⇒
  preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A)
    (^deletion_create A) (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_exact_preserves_create:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact m ⇒
  preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A)
    (^deletion_create A) m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_create_deletion_create:
  ¬account_already_created (lookup_account address A) ⇒
  preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A)
    (^deletion_create A) (proceed_create sender address value code gas)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem fixed_accounts_get_accounts_eq:
  preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A) R (f A) ⇒
  preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A) R
    (bind get_accounts f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem abort_create_exists_deletion_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact
    (abort_create_exists sender)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_create_deletion_create:
  preserves_when (λs. s.contexts ≠ [] ∧ s.rollback.accounts = A)
    (^deletion_create A) (step_create two)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_create_deletion_projections:
  s.contexts ≠ [] ∧ step_create two s = (r,t) ⇒
  ^deletion_create s.rollback.accounts s t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_create_deletion_exact:
  preserves_when (λs. s.contexts ≠ []) ^deletion_exact (handle_create e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem pop_context_deletion_projections:
  2 ≤ LENGTH s.contexts ∧
  pop_and_incorporate_context success s = (r,t) ⇒
  t.contexts ≠ [] ∧
  t.originalAccounts = s.originalAccounts ∧
  (t.rollback.toDelete = s.rollback.toDelete ∨
   t.rollback.toDelete = (SND (HD s.contexts)).toDelete) ∧
  LENGTH s.contexts = SUC (LENGTH t.contexts) ∧
  MAP (λp. (SND p).toDelete) t.contexts =
    TL (MAP (λp. (SND p).toDelete) s.contexts)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_exception_deletion_projections:
  s.contexts ≠ [] ∧ handle_exception e s = (r,t) ⇒
  t.contexts ≠ [] ∧
  t.originalAccounts = s.originalAccounts ∧
  (t.rollback.toDelete = s.rollback.toDelete ∨
   (2 ≤ LENGTH s.contexts ∧
    t.rollback.toDelete = (SND (HD s.contexts)).toDelete)) ∧
  ((LENGTH t.contexts = LENGTH s.contexts ∧
    MAP (λp. (SND p).toDelete) t.contexts =
      MAP (λp. (SND p).toDelete) s.contexts) ∨
   (2 ≤ LENGTH s.contexts ∧
    LENGTH s.contexts = SUC (LENGTH t.contexts) ∧
    MAP (λp. (SND p).toDelete) t.contexts =
      TL (MAP (λp. (SND p).toDelete) s.contexts)))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_step_deletion_projections:
  s.contexts ≠ [] ∧ handle_step e s = (r,t) ⇒
  t.contexts ≠ [] ∧
  t.originalAccounts = s.originalAccounts ∧
  (t.rollback.toDelete = s.rollback.toDelete ∨
   (2 ≤ LENGTH s.contexts ∧
    t.rollback.toDelete = (SND (HD s.contexts)).toDelete)) ∧
  ((LENGTH t.contexts = LENGTH s.contexts ∧
    MAP (λp. (SND p).toDelete) t.contexts =
      MAP (λp. (SND p).toDelete) s.contexts) ∨
   (2 ≤ LENGTH s.contexts ∧
    LENGTH s.contexts = SUC (LENGTH t.contexts) ∧
    MAP (λp. (SND p).toDelete) t.contexts =
      TL (MAP (λp. (SND p).toDelete) s.contexts)))
Proof
  cheat  (* SCAFFOLD *)
QED

(* Account-protection boundaries. *)
Theorem collision_free_nonce_code:
  ¬account_already_created acc ⇒ acc.nonce = 0 ∧ acc.code = []
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem increment_nonce_lookup:
  (lookup_account a (increment_nonce b accounts)).nonce =
    if a = b then SUC (lookup_account a accounts).nonce
    else (lookup_account a accounts).nonce
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem increment_nonce_code:
  (lookup_account a (increment_nonce b accounts)).code =
    (lookup_account a accounts).code
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deposit_code_nonce:
  (lookup_account a
    (update_account b (lookup_account b accounts with code := code)
      accounts)).nonce = (lookup_account a accounts).nonce
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deposit_code_other:
  a ≠ b ⇒
  lookup_account a
    (update_account b (lookup_account b accounts with code := code)
      accounts) = lookup_account a accounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_create_nonce_certificate:
  s.contexts ≠ [] ∧
  proceed_create sender address value code gas s = (r, t) ⇒
  0 < (lookup_account address t.rollback.accounts).nonce ∧
  (FST (HD t.contexts)).msgParams.outputTo = Code address
Proof
  cheat  (* SCAFFOLD *)
QED

val push_post = ``λQ (m:execution_state -> ('a + exception option) # execution_state). ∀s r t.
  m s = (r,t) ∧ s.contexts ≠ [] ∧
  LENGTH s.contexts < LENGTH t.contexts ⇒ Q s t``;

Theorem push_post_bind:
  preserves R g ∧
  (∀s u. R s u ⇒ (s.contexts ≠ [] ⇒ u.contexts ≠ []) ∧
                       LENGTH u.contexts = LENGTH s.contexts) ∧
  (∀s u t. R s u ∧ Q u t ⇒ Q s t) ∧
  (∀x. ^push_post Q (f x)) ⇒
  ^push_post Q (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem push_post_bind_psf:
  preserves_same_frame g ∧
  (∀x. ^push_post (λs t. P t) (f x)) ⇒
  ^push_post (λs t. P t) (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem push_post_ignore_bind_psf:
  preserves_same_frame g ∧ ^push_post (λs t. P t) f ⇒
  ^push_post (λs t. P t) (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem push_post_cond:
  ^push_post Q f ∧ ^push_post Q g ⇒
  ^push_post Q (if b then f else g)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem push_post_nongrowing:
  (∀s r t. m s = (r,t) ∧ s.contexts ≠ [] ⇒
    LENGTH t.contexts ≤ LENGTH s.contexts) ⇒ ^push_post Q m
Proof
  cheat  (* SCAFFOLD *)
QED

val push_post_unit = inst [alpha |-> ``:unit``] push_post;

Theorem proceed_create_nonce_certificate_prefix:
  preserves_same_frame g ⇒
  ^push_post_unit (λs t.
    0 < (lookup_account address t.rollback.accounts).nonce ∧
    (FST (HD t.contexts)).msgParams.outputTo = Code address)
    (bind g (λx. proceed_create sender address value code gas))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_create_growth_nonce_certificate:
  ^push_post_unit (λs t. ∀b.
    (FST (HD t.contexts)).msgParams.outputTo = Code b ⇒
    0 < (lookup_account b t.rollback.accounts).nonce) (step_create two)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_call_memory_output:
  s.contexts ≠ [] ∧
  proceed_call op sender address value ao az code stipend (Memory mr) s = (r,t) ⇒
  (FST (HD t.contexts)).msgParams.outputTo = Memory mr
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_growth_not_code:
  ^push_post_unit (λs t. ∀b.
    (FST (HD t.contexts)).msgParams.outputTo ≠ Code b) (step_call op)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Nonce/code transport before the return-code deposit boundary. *)
val nonce_code_rel = ``λa (s:execution_state) (t:execution_state).
  (lookup_account a s.rollback.accounts).nonce ≤
    (lookup_account a t.rollback.accounts).nonce ∧
  (lookup_account a t.rollback.accounts).code =
    (lookup_account a s.rollback.accounts).code``;

Theorem nonce_code_rel_trans:
  ^nonce_code_rel a s u ∧ ^nonce_code_rel a u t ⇒
  ^nonce_code_rel a s t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_nonce_code_of_rollback:
  preserves_rollback m ⇒ preserves (^nonce_code_rel a) m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_nonce_code_bind:
  preserves (^nonce_code_rel a) g ∧
  (∀x. preserves (^nonce_code_rel a) (f x)) ⇒
  preserves (^nonce_code_rel a) (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_nonce_code_ignore_bind:
  preserves (^nonce_code_rel a) g ∧
  preserves (^nonce_code_rel a) f ⇒
  preserves (^nonce_code_rel a) (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_nonce_code_increment:
  preserves (^nonce_code_rel a) (update_accounts (increment_nonce b))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_nonce_code_transfer:
  preserves (^nonce_code_rel a)
    (update_accounts (transfer_value sender recipient value))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_nonce_code_proceed_create:
  preserves (^nonce_code_rel a)
    (proceed_create sender address value code gas)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_nonce_code_access_address:
  preserves (^nonce_code_rel a) (access_address b)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_nonce_code_step_create:
  preserves (^nonce_code_rel a) (step_create two)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_nonce_code_proceed_call:
  preserves (^nonce_code_rel a)
    (proceed_call op sender address value off sz code gas output)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_nonce_code_step_call:
  preserves (^nonce_code_rel a) (step_call op)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_nonce_code_access_slot:
  preserves (^nonce_code_rel a) (access_slot sk)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_nonce_code_write_storage:
  preserves (^nonce_code_rel a) (write_storage b k v)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_nonce_code_sstore_gas:
  preserves (^nonce_code_rel a) (step_sstore_gas_consumption b k v)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_nonce_code_step_sstore:
  preserves (^nonce_code_rel a) (step_sstore transient)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_nonce_code_step_self_destruct:
  preserves (^nonce_code_rel a) step_self_destruct
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem cp_nonce_code:
  cp (m:unit execution) ⇒ preserves_when (λs. s.contexts ≠ []) (^nonce_code_rel a) m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inst_nonce_code:
  s.contexts ≠ [] ∧ step_inst op s = (r,t) ⇒ ^nonce_code_rel a s t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem set_last_accounts_foreign_lookup:
  ls ≠ [] ∧ a ≠ address ⇒
  MAP (λp. lookup_account a (SND p).accounts)
    (set_last_accounts (update_account address empty_account_state
      (SND (LAST ls)).accounts) ls) =
  MAP (λp. lookup_account a (SND p).accounts) ls
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_create_old_snapshot_lookups:
  s.contexts ≠ [] ∧ a ≠ address ∧
  proceed_create sender address value code gas s = (r,t) ⇒
  MAP (λp. lookup_account a (SND p).accounts) (TL t.contexts) =
  MAP (λp. lookup_account a (SND p).accounts) s.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_call_old_snapshot_lookups:
  proceed_call op sender address value ao az code gas rd s = (r,t) ∧
  s.contexts ≠ [] ∧ ¬fIN address precompile_addresses ⇒
  MAP (λp. lookup_account a (SND p).accounts) (TL t.contexts) =
  MAP (λp. lookup_account a (SND p).accounts) s.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_create_old_snapshot_lookups:
  step_create two s = (INL (),t) ∧ s.contexts ≠ [] ∧
  LENGTH s.contexts < LENGTH t.contexts ∧
  ((lookup_account a s.rollback.accounts).nonce ≠ 0 ∨
   ¬NULL (lookup_account a s.rollback.accounts).code) ⇒
  MAP (λp. lookup_account a (SND p).accounts) (TL t.contexts) =
  MAP (λp. lookup_account a (SND p).accounts) s.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_old_snapshot_lookups:
  step_call op s = (INL (),t) ∧ s.contexts ≠ [] ∧
  LENGTH s.contexts < LENGTH t.contexts ⇒
  MAP (λp. lookup_account a (SND p).accounts) (TL t.contexts) =
  MAP (λp. lookup_account a (SND p).accounts) s.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_growth_old_snapshot_lookups:
  wf_state s ∧ step s = (r,t) ∧ LENGTH s.contexts < LENGTH t.contexts ∧
  ((lookup_account a s.rollback.accounts).nonce ≠ 0 ∨
   ¬NULL (lookup_account a s.rollback.accounts).code) ⇒
  MAP (λp. lookup_account a (SND p).accounts) (TL t.contexts) =
  MAP (λp. lookup_account a (SND p).accounts) s.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_growth_old_snapshot_lookup:
  wf_state s ∧ step s = (r,t) ∧ LENGTH s.contexts < LENGTH t.contexts ∧
  ((lookup_account a s.rollback.accounts).nonce ≠ 0 ∨
   ¬NULL (lookup_account a s.rollback.accounts).code) ∧ i < LENGTH s.contexts ⇒
  lookup_account a (SND (EL (SUC i) t.contexts)).accounts =
  lookup_account a (SND (EL i s.contexts)).accounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_growth_nonce_code:
  wf_state s ∧ step s = (r,t) ∧ LENGTH s.contexts < LENGTH t.contexts ⇒
  ^nonce_code_rel a s t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_saved_head_accounts:
  step_call op s = (INL (),t) ∧ s.contexts ≠ [] ∧
  LENGTH s.contexts < LENGTH t.contexts ⇒
  (SND (HD t.contexts)).accounts = s.rollback.accounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_create_saved_head_nonce_code:
  step_create two s = (INL (),t) ∧ s.contexts ≠ [] ∧
  LENGTH s.contexts < LENGTH t.contexts ⇒
  (lookup_account a s.rollback.accounts).nonce ≤
    (lookup_account a (SND (HD t.contexts)).accounts).nonce ∧
  (lookup_account a (SND (HD t.contexts)).accounts).code =
    (lookup_account a s.rollback.accounts).code
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_growth_saved_head_nonce_code:
  wf_state s ∧ step s = (r,t) ∧ LENGTH s.contexts < LENGTH t.contexts ⇒
  (lookup_account a s.rollback.accounts).nonce ≤
    (lookup_account a (SND (HD t.contexts)).accounts).nonce ∧
  (lookup_account a (SND (HD t.contexts)).accounts).code =
    (lookup_account a s.rollback.accounts).code
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_growth_nonce_certificate:
  wf_state s ∧ step s = (r,t) ∧
  LENGTH s.contexts < LENGTH t.contexts ∧
  (FST (HD t.contexts)).msgParams.outputTo = Code b ⇒
  0 < (lookup_account b t.rollback.accounts).nonce
Proof
  cheat  (* SCAFFOLD *)
QED

Resume step_growth_nonce_certificate[inr]:
  simp[] >> rename1 `handle_step e u = (_, t)` >>
  `same_frame_or_grow inner` by simp[Abbr `inner`] >>
  `LENGTH s.contexts ≤ LENGTH u.contexts` by
    (drule_all same_frame_or_grow_length >> simp[]) >>
  strip_tac >>
  `u.contexts ≠ []` by (strip_tac >> gvs[]) >>
  `LENGTH t.contexts ≤ LENGTH s.contexts` suffices_by gvs[] >>
  Cases_on `LENGTH u.contexts = LENGTH s.contexts`
  >- (drule handle_step_shrinks_by_one >> simp[]) >>
  `LENGTH s.contexts < LENGTH u.contexts` by simp[] >>
  `outputTo_consistent s` by
    metis_tac[outputTo_consistent_stack_imp_consistent, wf_state_def] >>
  `¬vfm_abort e` by
    (irule step_inner_inr_grow_not_abort >>
     qexistsl_tac [`s`, `u`] >> simp[Abbr `inner`]) >>
  `0 < LENGTH s.contexts` by (Cases_on `s.contexts` >> gvs[]) >>
  `2 ≤ LENGTH u.contexts` by simp[] >>
  `LENGTH u.contexts = LENGTH s.contexts + 1` by
    (qunabbrev_tac `inner` >>
     drule_then drule step_inner_grows_by_exactly_one >> gvs[]) >>
  drule_at (Pat `handle_step`) handle_step_not_abort_pops >> gvs[] >>
  `decreases_gas_cred T 0 0 inner` suffices_by
    (gvs[decreases_gas_cred_def] >>
     disch_then (qspec_then `s` mp_tac) >> rw[] >>
     gvs[wf_state_def, EVERY_MEM]) >>
  simp[Abbr `inner`] >> irule decreases_gas_cred_bind_mono >>
  qexistsl_tac [`T`, `F`] >> simp[] >> gen_tac >>
  rw[] >> CASE_TAC >> rw[] >>
  irule decreases_gas_cred_ignore_bind_mono >> rw[] >>
  qexistsl_tac [`F`, `T`] >> simp[]
QED

Finalise step_growth_nonce_certificate

Theorem same_frame_nonce_monotone:
  same_frame_rel s t ⇒
  (lookup_account a s.rollback.accounts).nonce ≤
    (lookup_account a t.rollback.accounts).nonce
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_same_frame_positive_nonce:
  wf_state s ∧ step s = (r, t) ∧
  LENGTH t.contexts = LENGTH s.contexts ∧
  0 < (lookup_account a s.rollback.accounts).nonce ⇒
  0 < (lookup_account a t.rollback.accounts).nonce
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_create_nonce:
  s.contexts ≠ [] ∧ handle_create e s = (r, t) ⇒
  (lookup_account a t.rollback.accounts).nonce =
    (lookup_account a s.rollback.accounts).nonce
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_create_code_other:
  s.contexts ≠ [] ∧ handle_create e s = (r,t) ∧
  (FST (HD s.contexts)).msgParams.outputTo ≠ Code a ⇒
  (lookup_account a t.rollback.accounts).code =
    (lookup_account a s.rollback.accounts).code
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_create_protected_account:
  s.contexts ≠ [] ∧ handle_create e s = (r,t) ∧
  ((lookup_account a s.rollback.accounts).nonce ≠ 0 ∨
   ¬NULL (lookup_account a s.rollback.accounts).code) ∧
  ((FST (HD s.contexts)).msgParams.outputTo = Code a ⇒
    0 < (lookup_account a s.rollback.accounts).nonce) ⇒
  (lookup_account a t.rollback.accounts).nonce ≠ 0 ∨
    ¬NULL (lookup_account a t.rollback.accounts).code
Proof
  cheat  (* SCAFFOLD *)
QED

(* Depth-indexed bookkeeping for continuing run_call states.  Only the
 * newly pushed snapshots need account protection.  The initial saved head
 * can be restored at the terminal pop, but its deletion list is accessible. *)
val deletion_saved_absent = ``λn a (s:execution_state).
  ∀i. i < (if n = 1 then LENGTH s.contexts - 1
           else LENGTH s.contexts - n + 1) ⇒
    ¬MEM a (SND (EL i s.contexts)).toDelete``;

val deletion_saved_protected = ``λn a (s:execution_state).
  ∀i. i < LENGTH s.contexts - n ⇒
    (lookup_account a (SND (EL i s.contexts)).accounts).nonce ≠ 0 ∨
    ¬NULL (lookup_account a (SND (EL i s.contexts)).accounts).code``;

val deletion_creation_certificate = ``λn a (s:execution_state).
  ∀i. i < LENGTH s.contexts - n ∧
    (FST (EL i s.contexts)).msgParams.outputTo = Code a ⇒
    0 < (lookup_account a s.rollback.accounts).nonce ∧
    ∀j. j < i ⇒
      0 < (lookup_account a (SND (EL j s.contexts)).accounts).nonce``;

val deletion_run_inv = ``λn a original (s:execution_state).
  wf_state s ∧ n ≤ LENGTH s.contexts ∧
  ((lookup_account a s.rollback.accounts).nonce ≠ 0 ∨
    ¬NULL (lookup_account a s.rollback.accounts).code) ∧
  lookup_account a s.originalAccounts = original ∧
  ¬MEM a s.rollback.toDelete ∧
  ^deletion_saved_absent n a s ∧
  ^deletion_saved_protected n a s ∧
  ^deletion_creation_certificate n a s``;

Theorem deletion_run_inv_initial:
  wf_state s ∧ ¬MEM a s.rollback.toDelete ∧
  ¬(2 ≤ LENGTH s.contexts ∧ MEM a (SND (HD s.contexts)).toDelete) ∧
  ¬((lookup_account a s.rollback.accounts).nonce = 0 ∧
     NULL (lookup_account a s.rollback.accounts).code) ⇒
  ^deletion_run_inv (LENGTH s.contexts) a
    (lookup_account a s.originalAccounts) s
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_head_creation_certificate:
  ^deletion_creation_certificate n a s ∧ n < LENGTH s.contexts ∧
  (FST (HD s.contexts)).msgParams.outputTo = Code a ⇒
  0 < (lookup_account a s.rollback.accounts).nonce
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_pop_at_initial_depth_terminal:
  n = LENGTH s.contexts ∧ LENGTH t.contexts < LENGTH s.contexts ⇒
  ¬(n ≤ LENGTH t.contexts)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_saved_absent_push:
  0 < n ∧ n ≤ LENGTH s.contexts ∧
  LENGTH t.contexts = SUC (LENGTH s.contexts) ∧
  ^deletion_saved_absent n a s ∧
  ¬MEM a (SND (HD t.contexts)).toDelete ∧
  (∀i. i < LENGTH s.contexts ⇒
    (SND (EL (SUC i) t.contexts)).toDelete =
      (SND (EL i s.contexts)).toDelete) ⇒
  ^deletion_saved_absent n a t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_saved_absent_pop:
  0 < n ∧ n ≤ LENGTH t.contexts ∧
  LENGTH s.contexts = SUC (LENGTH t.contexts) ∧
  ^deletion_saved_absent n a s ∧
  (∀i. i < LENGTH t.contexts ⇒
    (SND (EL i t.contexts)).toDelete =
      (SND (EL (SUC i) s.contexts)).toDelete) ⇒
  ^deletion_saved_absent n a t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_saved_protected_push:
  0 < n ∧ n ≤ LENGTH s.contexts ∧
  LENGTH t.contexts = SUC (LENGTH s.contexts) ∧
  ^deletion_saved_protected n a s ∧
  ((lookup_account a (SND (HD t.contexts)).accounts).nonce ≠ 0 ∨
   ¬NULL (lookup_account a (SND (HD t.contexts)).accounts).code) ∧
  (∀i. i < LENGTH s.contexts ⇒
    lookup_account a (SND (EL (SUC i) t.contexts)).accounts =
      lookup_account a (SND (EL i s.contexts)).accounts) ⇒
  ^deletion_saved_protected n a t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_saved_protected_pop:
  0 < n ∧ n ≤ LENGTH t.contexts ∧
  LENGTH s.contexts = SUC (LENGTH t.contexts) ∧
  ^deletion_saved_protected n a s ∧
  (∀i. i < LENGTH t.contexts ⇒
    lookup_account a (SND (EL i t.contexts)).accounts =
      lookup_account a (SND (EL (SUC i) s.contexts)).accounts) ⇒
  ^deletion_saved_protected n a t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_saved_absent_same_depth:
  0 < n ∧ n ≤ LENGTH s.contexts ∧ LENGTH t.contexts = LENGTH s.contexts ∧
  ^deletion_saved_absent n a s ∧
  (∀i. i < LENGTH s.contexts ⇒
    (SND (EL i t.contexts)).toDelete = (SND (EL i s.contexts)).toDelete) ⇒
  ^deletion_saved_absent n a t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_saved_protected_same_depth:
  0 < n ∧ n ≤ LENGTH s.contexts ∧ LENGTH t.contexts = LENGTH s.contexts ∧
  ^deletion_saved_protected n a s ∧
  (∀i. i < LENGTH s.contexts ⇒
    lookup_account a (SND (EL i t.contexts)).accounts =
      lookup_account a (SND (EL i s.contexts)).accounts) ⇒
  ^deletion_saved_protected n a t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_creation_certificate_push:
  0 < n ∧ n ≤ LENGTH s.contexts ∧
  LENGTH t.contexts = SUC (LENGTH s.contexts) ∧
  ^deletion_creation_certificate n a s ∧
  (lookup_account a s.rollback.accounts).nonce ≤
    (lookup_account a t.rollback.accounts).nonce ∧
  (lookup_account a s.rollback.accounts).nonce ≤
    (lookup_account a (SND (HD t.contexts)).accounts).nonce ∧
  ((FST (HD t.contexts)).msgParams.outputTo = Code a ⇒
    0 < (lookup_account a t.rollback.accounts).nonce) ∧
  (∀i. i < LENGTH s.contexts ⇒
    lookup_account a (SND (EL (SUC i) t.contexts)).accounts =
      lookup_account a (SND (EL i s.contexts)).accounts) ∧
  (∀i. i < LENGTH s.contexts ⇒
    (FST (EL (SUC i) t.contexts)).msgParams.outputTo =
      (FST (EL i s.contexts)).msgParams.outputTo) ⇒
  ^deletion_creation_certificate n a t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_creation_certificate_pop:
  0 < n ∧ n ≤ LENGTH t.contexts ∧
  LENGTH s.contexts = SUC (LENGTH t.contexts) ∧
  ^deletion_creation_certificate n a s ∧
  (0 < (lookup_account a s.rollback.accounts).nonce ∧
   0 < (lookup_account a (SND (HD s.contexts)).accounts).nonce ⇒
     0 < (lookup_account a t.rollback.accounts).nonce) ∧
  (∀i. i < LENGTH t.contexts ⇒
    lookup_account a (SND (EL i t.contexts)).accounts =
      lookup_account a (SND (EL (SUC i) s.contexts)).accounts) ∧
  (∀i. i < LENGTH t.contexts ⇒
    (FST (EL i t.contexts)).msgParams.outputTo =
      (FST (EL (SUC i) s.contexts)).msgParams.outputTo) ⇒
  ^deletion_creation_certificate n a t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_creation_certificate_same_depth:
  0 < n ∧ n ≤ LENGTH s.contexts ∧ LENGTH t.contexts = LENGTH s.contexts ∧
  ^deletion_creation_certificate n a s ∧
  (lookup_account a s.rollback.accounts).nonce ≤
    (lookup_account a t.rollback.accounts).nonce ∧
  (∀i. i < LENGTH s.contexts ⇒
    lookup_account a (SND (EL i t.contexts)).accounts =
      lookup_account a (SND (EL i s.contexts)).accounts) ∧
  (∀i. i < LENGTH s.contexts ⇒
    (FST (EL i t.contexts)).msgParams.outputTo =
      (FST (EL i s.contexts)).msgParams.outputTo) ⇒
  ^deletion_creation_certificate n a t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_create_protected_original:
  s.contexts ≠ [] ∧ step_create two s = (r,t) ∧
  ((lookup_account a s.rollback.accounts).nonce ≠ 0 ∨
   ¬NULL (lookup_account a s.rollback.accounts).code) ⇒
  lookup_account a t.originalAccounts =
    lookup_account a s.originalAccounts
Proof
  cheat  (* SCAFFOLD *)
QED

val deletion_opcode = ``λa (s:execution_state) (t:execution_state).
  t.contexts ≠ [] ∧
  lookup_account a t.originalAccounts =
    lookup_account a s.originalAccounts ∧
  ¬MEM a t.rollback.toDelete ∧
  (MAP (λp. (SND p).toDelete) t.contexts =
     MAP (λp. (SND p).toDelete) s.contexts ∨
   MAP (λp. (SND p).toDelete) t.contexts =
     s.rollback.toDelete :: MAP (λp. (SND p).toDelete) s.contexts)``;

Theorem step_inst_deletion_opcode:
  s.contexts ≠ [] ∧ step_inst op s = (r,t) ∧
  ¬MEM a s.rollback.toDelete ∧
  ¬account_empty (lookup_account a s.originalAccounts) ∧
  ((lookup_account a s.rollback.accounts).nonce ≠ 0 ∨
   ¬NULL (lookup_account a s.rollback.accounts).code) ⇒
  ^deletion_opcode a s t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_opcode_exact_trans:
  ^deletion_opcode a s t ∧ ^deletion_exact t u ⇒
  ^deletion_opcode a s u
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inst_inc_pc_deletion_opcode:
  s.contexts ≠ [] ∧
  ignore_bind (step_inst op) (inc_pc_or_jump op) s = (r,t) ∧
  ¬MEM a s.rollback.toDelete ∧
  ¬account_empty (lookup_account a s.originalAccounts) ∧
  ((lookup_account a s.rollback.accounts).nonce ≠ 0 ∨
   ¬NULL (lookup_account a s.rollback.accounts).code) ⇒
  ^deletion_opcode a s t
Proof
  cheat  (* SCAFFOLD *)
QED

val deletion_step_inner = ``do
  context <- get_current_context;
  case FLOOKUP context.msgParams.parsed context.pc of
  | SOME op => ignore_bind (step_inst op) (inc_pc_or_jump op)
  | NONE => if LENGTH context.msgParams.code ≤ context.pc
            then step_inst Stop else step_inst Invalid
  od``;

Theorem step_inner_deletion_opcode:
  s.contexts ≠ [] ∧ ^deletion_step_inner s = (r,t) ∧
  ¬MEM a s.rollback.toDelete ∧
  ¬account_empty (lookup_account a s.originalAccounts) ∧
  ((lookup_account a s.rollback.accounts).nonce ≠ 0 ∨
   ¬NULL (lookup_account a s.rollback.accounts).code) ⇒
  ^deletion_opcode a s t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_saved_head_absent:
  0 < n ∧ n ≤ LENGTH s.contexts ∧ 2 ≤ LENGTH s.contexts ∧
  ^deletion_saved_absent n a s ⇒
  ¬MEM a (SND (HD s.contexts)).toDelete
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_opcode_saved_head_absent:
  0 < n ∧ n ≤ LENGTH s.contexts ∧
  ^deletion_saved_absent n a s ∧ ¬MEM a s.rollback.toDelete ∧
  ^deletion_opcode a s t ∧ 2 ≤ LENGTH t.contexts ⇒
  ¬MEM a (SND (HD t.contexts)).toDelete
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_deletion_absent:
  0 < n ∧ ^deletion_run_inv n a original s ∧
  ¬account_empty original ∧ step s = (r,t) ⇒
  ¬MEM a t.rollback.toDelete
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_protected_original:
  s.contexts ≠ [] ∧ step s = (r,t) ∧
  ¬MEM a s.rollback.toDelete ∧
  ¬account_empty (lookup_account a s.originalAccounts) ∧
  ((lookup_account a s.rollback.accounts).nonce ≠ 0 ∨
   ¬NULL (lookup_account a s.rollback.accounts).code) ⇒
  lookup_account a t.originalAccounts =
    lookup_account a s.originalAccounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inst_inc_pc_nonce_code:
  s.contexts ≠ [] ∧
  ignore_bind (step_inst op) (inc_pc_or_jump op) s = (r,t) ⇒
  ^nonce_code_rel a s t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inner_nonce_code:
  s.contexts ≠ [] ∧ ^deletion_step_inner s = (r,t) ⇒
  ^nonce_code_rel a s t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_exception_rollback_sources:
  s.contexts ≠ [] ∧ handle_exception e s = (r,t) ⇒
  t.rollback = s.rollback ∨
  (2 ≤ LENGTH s.contexts ∧ t.rollback = SND (HD s.contexts))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_step_nonce_sources:
  s.contexts ≠ [] ∧ handle_step e s = (r,t) ⇒
  (lookup_account a t.rollback.accounts).nonce =
    (lookup_account a s.rollback.accounts).nonce ∨
  (2 ≤ LENGTH s.contexts ∧
   (lookup_account a t.rollback.accounts).nonce =
     (lookup_account a (SND (HD s.contexts)).accounts).nonce)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_step_protected_account:
  s.contexts ≠ [] ∧ handle_step e s = (r,t) ∧
  ((lookup_account a s.rollback.accounts).nonce ≠ 0 ∨
   ¬NULL (lookup_account a s.rollback.accounts).code) ∧
  (2 ≤ LENGTH s.contexts ⇒
    (lookup_account a (SND (HD s.contexts)).accounts).nonce ≠ 0 ∨
    ¬NULL (lookup_account a (SND (HD s.contexts)).accounts).code) ∧
  ((FST (HD s.contexts)).msgParams.outputTo = Code a ⇒
    0 < (lookup_account a s.rollback.accounts).nonce) ⇒
  (lookup_account a t.rollback.accounts).nonce ≠ 0 ∨
    ¬NULL (lookup_account a t.rollback.accounts).code
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_handle_exception_inl_pops:
  s.contexts ≠ [] ∧ handle_exception e s = (INL x,t) ⇒
  LENGTH t.contexts + 1 = LENGTH s.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_handle_step_inl_pops:
  s.contexts ≠ [] ∧ handle_step e s = (INL x,t) ⇒
  LENGTH t.contexts + 1 = LENGTH s.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_inner_inr_grow_protected_head:
  wf_state s ∧ ^deletion_step_inner s = (INR e,u) ∧
  LENGTH s.contexts < LENGTH u.contexts ∧
  ((lookup_account a s.rollback.accounts).nonce ≠ 0 ∨
   ¬NULL (lookup_account a s.rollback.accounts).code) ⇒
  (∃mr. (FST (HD u.contexts)).msgParams.outputTo = Memory mr) ∧
  ((lookup_account a (SND (HD u.contexts)).accounts).nonce ≠ 0 ∨
   ¬NULL (lookup_account a (SND (HD u.contexts)).accounts).code)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_deletion_continuing_protected:
  0 < n ∧ ^deletion_run_inv n a original s ∧
  step s = (INL x,t) ∧ n ≤ LENGTH t.contexts ⇒
  (lookup_account a t.rollback.accounts).nonce ≠ 0 ∨
  ¬NULL (lookup_account a t.rollback.accounts).code
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_step_pop_projections:
  wf_state s ∧ step s = (r,t) ∧ LENGTH t.contexts < LENGTH s.contexts ⇒
  LENGTH s.contexts = SUC (LENGTH t.contexts) ∧
  (∀i. i < LENGTH t.contexts ⇒
    SND (EL i t.contexts) = SND (EL (SUC i) s.contexts) ∧
    (FST (EL i t.contexts)).msgParams.outputTo =
      (FST (EL (SUC i) s.contexts)).msgParams.outputTo)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem deletion_same_frame_saved_projections:
  same_frame_rel s t ∧ i < LENGTH s.contexts ⇒
  SND (EL i t.contexts) = SND (EL i s.contexts) ∧
  (FST (EL i t.contexts)).msgParams.outputTo =
    (FST (EL i s.contexts)).msgParams.outputTo
Proof
  cheat  (* SCAFFOLD *)
QED


Theorem step_deletion_continuing_saved_protected:
  0 < n ∧ ^deletion_run_inv n a original s ∧
  ¬account_empty original ∧ step s = (INL x,t) ∧ n ≤ LENGTH t.contexts ⇒
  ^deletion_saved_protected n a t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_deletion_continuing_saved_absent:
  0 < n ∧ ^deletion_run_inv n a original s ∧
  ¬account_empty original ∧ step s = (INL x,t) ∧ n ≤ LENGTH t.contexts ⇒
  ^deletion_saved_absent n a t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_growth_shifted_output:
  wf_state s ∧ step s = (r,t) ∧ LENGTH s.contexts < LENGTH t.contexts ∧
  i < LENGTH s.contexts ⇒
  (FST (EL (SUC i) t.contexts)).msgParams.outputTo =
  (FST (EL i s.contexts)).msgParams.outputTo
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_pop_positive_nonce:
  wf_state s ∧ step s = (r,t) ∧ LENGTH t.contexts < LENGTH s.contexts ∧
  0 < (lookup_account a s.rollback.accounts).nonce ∧
  0 < (lookup_account a (SND (HD s.contexts)).accounts).nonce ⇒
  0 < (lookup_account a t.rollback.accounts).nonce
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_deletion_continuing_creation_certificate:
  0 < n ∧ ^deletion_run_inv n a original s ∧
  ¬account_empty original ∧ step s = (INL x,t) ∧ n ≤ LENGTH t.contexts ⇒
  ^deletion_creation_certificate n a t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_deletion_continuing_inv:
  0 < n ∧ ^deletion_run_inv n a original s ∧
  ¬account_empty original ∧ step s = (INL x,t) ∧ n ≤ LENGTH t.contexts ⇒
  ^deletion_run_inv n a original t
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_call_to_delete:
  wf_state es ∧
  run_call es = SOME (r, es') ∧
  MEM a es'.rollback.toDelete ⇒
  MEM a es.rollback.toDelete ∨
  (2 ≤ LENGTH es.contexts ∧ MEM a (SND (HD es.contexts)).toDelete) ∨
  account_empty (lookup_account a es.originalAccounts) ∨
  (lookup_account a es.rollback.accounts).nonce = 0 ∧
  NULL (lookup_account a es.rollback.accounts).code
Proof
  cheat  (* SCAFFOLD *)
QED
