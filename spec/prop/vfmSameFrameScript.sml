(*
 * Same-frame preservation framework.
 *
 * `same_frame_rel s s'` is a relation expressing what necessarily holds
 * between states `s` and `s'` whenever `s'` is reached from `s` by
 * execution that does not push or pop the call stack — i.e. while
 * staying strictly within the current call frame.
 *
 * This theory establishes:
 *   - the base relation `same_frame_rel` (reflexive, transitive);
 *   - the monadic property `preserves_same_frame`, closed under all
 *     monad combinators, plus primitive / opcode / precompile [simp]
 *     lemmas;
 *   - the state-indexed analogue `psf`, with getter-bind specialisations
 *     for threading "x = head's callee"-style invariants into
 *     continuations, and rollback-writer leaves used to prove SSTORE
 *     and `abort_create_exists` preserve the frame;
 *   - `outputTo_consistent`, a well-formedness predicate on the head
 *     context preserved by `same_frame_rel`;
 *   - SELFDESTRUCT psf details (transfer_value preserves storage /
 *     code / nonce);
 *   - `proceed_call_length`, `proceed_create_length`: the length of
 *     the contexts stack after proceed_call / proceed_create is at
 *     least (resp. exactly) one more than before;
 *   - the utility bridges `cp_imp_length_contexts_preserved` and
 *     `psf_imp_length_contexts_preserved`.
 *
 * Downstream theories (`vfmStepLength`, `vfmHandleStep`,
 * `vfmRunWithinFrame`, `vfmRunCall`, ...) use this relation and its
 * companion frameworks to lift preservation properties through
 * `run_within_frame`, `run_call`, and `run`.
 *
 * Companion theories:
 *   - `vfmStepLength` adds `same_frame_or_grow` / `psf_or_grow` /
 *     `length_preserves` for reasoning about step_call / step_create.
 *   - `vfmMsdomainPreserved` proves msdomain is preserved exactly
 *     through handle_step.
 *   - `vfmHandleStep` proves handle-layer same-frame and pop-effect
 *     lemmas.
 *   - `vfmRunWithinFrame` composes all of the above into the
 *     `run_within_frame_preserves_*` headline theorems.
 *)
Theory vfmSameFrame
Ancestors
  arithmetic combin list pair pred_set finite_set rich_list
  vfmState vfmContext vfmExecution vfmExecutionProp
  vfmStaticCalls vfmTxParams vfmDomainSeparation vfmDecreasesGas
  vfmPreserves
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
  cheat  (* SCAFFOLD *)
QED

Theorem msdomain_compatible_trans:
  msdomain_compatible m1 m2 ∧ msdomain_compatible m2 m3 ⇒
  msdomain_compatible m1 m3
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

Theorem callee_local_changes_trans:
  callee_local_changes callee r1 r2 ∧
  callee_local_changes callee r2 r3 ⇒
  callee_local_changes callee r1 r3
Proof
  cheat  (* SCAFFOLD *)
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
    s'.originalAccounts = s.originalAccounts ∧
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
  cheat  (* SCAFFOLD *)
QED

(* ================================================================ *)
(* Transitivity.                                                     *)
(* ================================================================ *)

Theorem same_frame_rel_trans:
  same_frame_rel s1 s2 ∧ same_frame_rel s2 s3 ⇒
  same_frame_rel s1 s3
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem same_frame_rel_contexts_ne:
  same_frame_rel s s' ⇒ s'.contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
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

Theorem preserves_same_frame_eq_preserves_when:
  preserves_same_frame m ⇔ preserves_when (λs. s.contexts ≠ []) same_frame_rel m
Proof
  cheat  (* SCAFFOLD *)
QED

(* ---------------- Composition lemmas ---------------- *)

Theorem preserves_same_frame_bind[simp]:
  preserves_same_frame g ∧ (∀x. preserves_same_frame (f x)) ⇒
  preserves_same_frame (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_ignore_bind[simp]:
  preserves_same_frame g ∧ preserves_same_frame f ⇒
  preserves_same_frame (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

(* When g is preserves_same_frame and bind g f grows, we can extract
   the intermediate state sm with same_frame_rel s sm. This is useful
   for peeling prefix operations when proving structural facts about
   push operations like step_call/step_create. *)
Theorem bind_psf_grows_extract:
  preserves_same_frame g ∧
  bind g f s = (r, s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts
  ⇒
  ∃x sm. g s = (INL x, sm) ∧ same_frame_rel s sm ∧ f x sm = (r, s')
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_handle[simp]:
  preserves_same_frame f ∧ (∀e. preserves_same_frame (h e)) ⇒
  preserves_same_frame (handle f h)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_cond[simp]:
  preserves_same_frame m1 ∧ preserves_same_frame m2 ⇒
  preserves_same_frame (if b then m1 else m2)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_case_option[simp]:
  preserves_same_frame m_none ∧ (∀x. preserves_same_frame (m_some x)) ⇒
  preserves_same_frame (case opt of NONE => m_none | SOME x => m_some x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_case_sum[simp]:
  (∀x. preserves_same_frame (f x)) ∧ (∀y. preserves_same_frame (g y)) ⇒
  preserves_same_frame (case s of INL x => f x | INR y => g y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_case_pair[simp]:
  (∀x y. preserves_same_frame (f x y)) ⇒
  preserves_same_frame (case p of (x, y) => f x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_let[simp]:
  (∀x. preserves_same_frame (f x)) ⇒
  preserves_same_frame (let x = v in f x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_uncurry[simp]:
  (∀x y. preserves_same_frame (f x y)) ⇒
  preserves_same_frame (UNCURRY f p)
Proof
  cheat  (* SCAFFOLD *)
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
         get_original_def, bind_def, ignore_bind_def]
  \\ gvs[AllCaseEqs()]
  \\ irule same_frame_rel_refl \\ simp[];

Theorem preserves_same_frame_return[simp]:
  preserves_same_frame (return x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_fail[simp]:
  preserves_same_frame (fail e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_reraise[simp]:
  preserves_same_frame (reraise eo)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_assert[simp]:
  preserves_same_frame (assert b e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_finish[simp]:
  preserves_same_frame finish
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_revert[simp]:
  preserves_same_frame revert
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_get_current_context[simp]:
  preserves_same_frame get_current_context
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_get_num_contexts[simp]:
  preserves_same_frame get_num_contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_get_tx_params[simp]:
  preserves_same_frame get_tx_params
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_get_accounts[simp]:
  preserves_same_frame get_accounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_get_rollback[simp]:
  preserves_same_frame get_rollback
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_get_tStorage[simp]:
  preserves_same_frame get_tStorage
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_get_gas_left[simp]:
  preserves_same_frame get_gas_left
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_get_callee[simp]:
  preserves_same_frame get_callee
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_get_caller[simp]:
  preserves_same_frame get_caller
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_get_value[simp]:
  preserves_same_frame get_value
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_get_static[simp]:
  preserves_same_frame get_static
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_get_output_to[simp]:
  preserves_same_frame get_output_to
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_get_return_data[simp]:
  preserves_same_frame get_return_data
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_get_return_data_check[simp]:
  preserves_same_frame (get_return_data_check offset sz)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_get_code[simp]:
  preserves_same_frame (get_code addr)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_get_current_code[simp]:
  preserves_same_frame get_current_code
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_get_call_data[simp]:
  preserves_same_frame get_call_data
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_get_original[simp]:
  preserves_same_frame get_original
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_read_memory[simp]:
  preserves_same_frame (read_memory offset sz)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_memory_expansion_info[simp]:
  preserves_same_frame (memory_expansion_info offset sz)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_assert_not_static[simp]:
  preserves_same_frame assert_not_static
Proof
  cheat  (* SCAFFOLD *)
QED

(* ---------------- Group B: head-context-only writers ------------ *)

(* These writers all go through `set_current_context` with a function
   of the head context that keeps `msgParams` fixed and adjusts only
   stack/memory/pc/jumpDest/returnData/gasUsed/logs/refunds. We prove
   each explicitly. *)

val psf_head_tac =
  rw[preserves_same_frame_def, same_frame_rel_def,
     bind_def, ignore_bind_def,
     get_current_context_def, set_current_context_def,
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
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_pop_stack[simp]:
  preserves_same_frame (pop_stack n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_consume_gas[simp]:
  preserves_same_frame (consume_gas n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_unuse_gas[simp]:
  preserves_same_frame (unuse_gas n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_set_return_data[simp]:
  preserves_same_frame (set_return_data rd)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_set_jump_dest[simp]:
  preserves_same_frame (set_jump_dest jd)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_inc_pc[simp]:
  preserves_same_frame inc_pc
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_expand_memory[simp]:
  preserves_same_frame (expand_memory n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_write_memory[simp]:
  preserves_same_frame (write_memory i bs)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_update_gas_refund[simp]:
  preserves_same_frame (update_gas_refund ars)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_push_logs[simp]:
  preserves_same_frame (push_logs ls)
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

(* `write_transient_storage` targets the callee's slot. *)

Theorem preserves_same_frame_write_transient_storage_callee:
  preserves_same_frame
    (do addr <- get_callee;
        write_transient_storage addr key value
     od)
Proof
  cheat  (* SCAFFOLD *)
QED

(* `write_storage` targets a specific account's storage; safe when
   that address is the head's callee. *)

Theorem preserves_same_frame_write_storage_callee:
  preserves_same_frame
    (do addr <- get_callee;
        write_storage addr key value
     od)
Proof
  cheat  (* SCAFFOLD *)
QED

(* `update_accounts (increment_nonce callee)`: safe; increments callee
   nonce only. *)

Theorem preserves_same_frame_update_accounts_increment_nonce_callee:
  preserves_same_frame
    (do addr <- get_callee;
        update_accounts (increment_nonce addr)
     od)
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

Theorem write_transient_storage_same_frame:
  s.contexts ≠ [] ∧
  address = (FST (HD s.contexts)).msgParams.callee ⇒
  same_frame_rel s (SND (write_transient_storage address key value s))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem update_accounts_increment_nonce_same_frame:
  s.contexts ≠ [] ∧
  address = (FST (HD s.contexts)).msgParams.callee ⇒
  same_frame_rel s
    (SND (update_accounts (increment_nonce address) s))
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

(* ---------------- Group E: domain / access writers -------------- *)

Theorem preserves_same_frame_set_domain:
  msdomain_compatible s.msdomain d ∧ s.contexts ≠ [] ⇒
  same_frame_rel s (SND (set_domain d s))
Proof
  cheat  (* SCAFFOLD *)
QED

(* `domain_check`: in Enforce mode it either continues via `cont` or
   fails leaving state untouched; in Collect mode it updates msdomain
   (compatibly) then runs `cont`. *)

Theorem preserves_same_frame_domain_check:
  (∀d. subdomain d (add d)) ∧
  preserves_same_frame cont ⇒
  preserves_same_frame (domain_check err check add cont)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_access_address[simp]:
  preserves_same_frame (access_address a)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_access_slot[simp]:
  preserves_same_frame (access_slot sk)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_ensure_storage_in_domain[simp]:
  preserves_same_frame (ensure_storage_in_domain a)
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_monop[simp]:
  preserves_same_frame (step_monop op f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_modop[simp]:
  preserves_same_frame (step_modop op f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_context[simp]:
  preserves_same_frame (step_context op f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_msgParams[simp]:
  preserves_same_frame (step_msgParams op f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_txParams[simp]:
  preserves_same_frame (step_txParams op f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_exp[simp]:
  preserves_same_frame step_exp
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_keccak256[simp]:
  preserves_same_frame step_keccak256
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_sload[simp]:
  preserves_same_frame (step_sload t)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_sstore_gas_consumption[simp]:
  preserves_same_frame (step_sstore_gas_consumption a k v)
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_call_data_load[simp]:
  preserves_same_frame step_call_data_load
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_copy_to_memory:
  (∀f. src = SOME f ⇒ preserves_same_frame f) ⇒
  preserves_same_frame (copy_to_memory gas off srcOff sz src)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_copy_to_memory[simp]:
  (∀f. src = SOME f ⇒ preserves_same_frame f) ⇒
  preserves_same_frame (step_copy_to_memory op src)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_return_data_copy[simp]:
  preserves_same_frame step_return_data_copy
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_ext_code_size[simp]:
  preserves_same_frame step_ext_code_size
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_ext_code_copy[simp]:
  preserves_same_frame step_ext_code_copy
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_ext_code_hash[simp]:
  preserves_same_frame step_ext_code_hash
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_block_hash[simp]:
  preserves_same_frame step_block_hash
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_blob_hash[simp]:
  preserves_same_frame step_blob_hash
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_self_balance[simp]:
  preserves_same_frame step_self_balance
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_mload[simp]:
  preserves_same_frame step_mload
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_mstore[simp]:
  preserves_same_frame (step_mstore op)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_jump[simp]:
  preserves_same_frame step_jump
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_jumpi[simp]:
  preserves_same_frame step_jumpi
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_push[simp]:
  preserves_same_frame (step_push n ws)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_pop[simp]:
  preserves_same_frame step_pop
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_dup[simp]:
  preserves_same_frame (step_dup n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_dupn[simp]:
  preserves_same_frame step_dupn
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_swapn[simp]:
  preserves_same_frame step_swapn
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_exchange[simp]:
  preserves_same_frame step_exchange
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_swap[simp]:
  preserves_same_frame (step_swap n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_log[simp]:
  preserves_same_frame (step_log n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_return[simp]:
  preserves_same_frame (step_return b)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_inc_pc_or_jump[simp]:
  preserves_same_frame (inc_pc_or_jump op)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_abort_unuse[simp]:
  preserves_same_frame (abort_unuse n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_abort_call_value[simp]:
  preserves_same_frame (abort_call_value n)
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_precompile_sha2_256[simp]:
  preserves_same_frame precompile_sha2_256
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_precompile_ripemd_160[simp]:
  preserves_same_frame precompile_ripemd_160
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_precompile_identity[simp]:
  preserves_same_frame precompile_identity
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_precompile_modexp[simp]:
  preserves_same_frame precompile_modexp
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_precompile_ecadd[simp]:
  preserves_same_frame precompile_ecadd
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_precompile_ecmul[simp]:
  preserves_same_frame precompile_ecmul
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_precompile_ecpairing[simp]:
  preserves_same_frame precompile_ecpairing
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_precompile_blake2f[simp]:
  preserves_same_frame precompile_blake2f
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_precompile_point_eval[simp]:
  preserves_same_frame precompile_point_eval
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_precompile_bls_g1add[simp]:
  preserves_same_frame precompile_bls_g1add
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_precompile_bls_g1msm[simp]:
  preserves_same_frame precompile_bls_g1msm
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_precompile_bls_g2add[simp]:
  preserves_same_frame precompile_bls_g2add
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_precompile_bls_g2msm[simp]:
  preserves_same_frame precompile_bls_g2msm
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_precompile_bls_pairing[simp]:
  preserves_same_frame precompile_bls_pairing
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_precompile_bls_map_fp_to_g1[simp]:
  preserves_same_frame precompile_bls_map_fp_to_g1
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_precompile_bls_map_fp2_to_g2[simp]:
  preserves_same_frame precompile_bls_map_fp2_to_g2
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_precompile_p256verify[simp]:
  preserves_same_frame precompile_p256verify
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_dispatch_precompiles[simp]:
  preserves_same_frame (dispatch_precompiles a)
Proof
  cheat  (* SCAFFOLD *)
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

Theorem psf_eq_preserves_when:
  psf p m ⇔ preserves_when (λs. p s ∧ s.contexts ≠ []) same_frame_rel m
Proof
  cheat  (* SCAFFOLD *)
QED

(* ---------------- Monotonicity and bridges --------------------- *)

Theorem psf_mono:
  psf p m ∧ (∀s. q s ⇒ p s) ⇒ psf q m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_eq_psf_T:
  preserves_same_frame m ⇔ psf (λs. T) m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_imp_psf:
  preserves_same_frame m ⇒ psf p m
Proof
  cheat  (* SCAFFOLD *)
QED

(* Simp rule: any preserves_same_frame fact auto-lifts to psf p. *)
Theorem psf_of_preserves_same_frame[simp]:
  preserves_same_frame m ⇒ psf p m
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

Theorem psf_ignore_bind:
  psf p g ∧ psf p_cont f ∧
  (∀s s'. g s = (INL (), s') ∧ p s ∧ s.contexts ≠ [] ⇒ p_cont s') ⇒
  psf p (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_handle:
  psf p f ∧
  (∀e. psf (p_handler e) (h e)) ∧
  (∀e s s'. f s = (INR e, s') ∧ p s ∧ s.contexts ≠ [] ⇒
            p_handler e s') ⇒
  psf p (handle f h)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_cond:
  psf p m1 ∧ psf p m2 ⇒ psf p (if b then m1 else m2)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_case_option:
  psf p m_none ∧ (∀x. psf p (m_some x)) ⇒
  psf p (case opt of NONE => m_none | SOME x => m_some x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_case_sum:
  (∀x. psf p (f x)) ∧ (∀y. psf p (g y)) ⇒
  psf p (case sm of INL x => f x | INR y => g y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_case_pair:
  (∀x y. psf p (f x y)) ⇒ psf p (case pr of (x, y) => f x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_let:
  (∀x. psf p (f x)) ⇒ psf p (let x = v in f x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_uncurry:
  (∀x y. psf p (f x y)) ⇒ psf p (UNCURRY f pr)
Proof
  cheat  (* SCAFFOLD *)
QED

(* ---------------- `same_frame_rel` extractors ------------------- *)

Theorem same_frame_rel_msgParams:
  same_frame_rel s s' ⇒
  (FST (HD s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem same_frame_rel_callee:
  same_frame_rel s s' ⇒
  (FST (HD s'.contexts)).msgParams.callee =
  (FST (HD s.contexts)).msgParams.callee
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem same_frame_rel_contexts_ne_src:
  same_frame_rel s s' ⇒ s.contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

(* `psf p m` implies the continuation's state has the same head callee
   as the original, provided p implied contexts ≠ []. *)
Theorem psf_preserves_head_callee:
  psf p m ∧ m s = (r, s') ∧ p s ∧ s.contexts ≠ [] ⇒
  (FST (HD s'.contexts)).msgParams.callee =
  (FST (HD s.contexts)).msgParams.callee
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_preserves_head_msgParams:
  psf p m ∧ m s = (r, s') ∧ p s ∧ s.contexts ≠ [] ⇒
  (FST (HD s'.contexts)).msgParams = (FST (HD s.contexts)).msgParams
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_preserves_contexts_ne:
  psf p m ∧ m s = (r, s') ∧ p s ∧ s.contexts ≠ [] ⇒
  s'.contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

(* ---------------- Specialised getter-bind rules ----------------- *)

(* For `bind get_callee f`, the continuation runs at the same state
   with `x = head's callee` available as a fact. *)
Theorem psf_bind_get_callee:
  (∀x. psf (λs. p s ∧ x = (FST (HD s.contexts)).msgParams.callee)
           (f x)) ⇒
  psf p (bind get_callee f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_bind_get_current_context:
  (∀x. psf (λs. p s ∧ s.contexts ≠ [] ∧ x = FST (HD s.contexts)) (f x)) ⇒
  psf p (bind get_current_context f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_bind_get_caller:
  (∀x. psf (λs. p s ∧ x = (FST (HD s.contexts)).msgParams.caller) (f x)) ⇒
  psf p (bind get_caller f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_bind_get_value:
  (∀x. psf (λs. p s ∧ x = (FST (HD s.contexts)).msgParams.value) (f x)) ⇒
  psf p (bind get_value f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_bind_get_accounts:
  (∀x. psf (λs. p s ∧ x = s.rollback.accounts) (f x)) ⇒
  psf p (bind get_accounts f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_bind_get_tStorage:
  (∀x. psf (λs. p s ∧ x = s.rollback.tStorage) (f x)) ⇒
  psf p (bind get_tStorage f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_bind_get_rollback:
  (∀x. psf (λs. p s ∧ x = s.rollback) (f x)) ⇒
  psf p (bind get_rollback f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_bind_get_tx_params:
  (∀x. psf (λs. p s ∧ x = s.txParams) (f x)) ⇒
  psf p (bind get_tx_params f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_bind_get_original_accounts:
  (∀x. psf (λs. p s ∧ s.contexts ≠ [] ∧
                 x = s.originalAccounts) (f x)) ⇒
  psf p (bind get_original f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_bind_get_original = psf_bind_get_original_accounts;

(* ---------------- Rollback-writer leaves ------------------------ *)

Theorem psf_write_storage:
  psf (λs. address = (FST (HD s.contexts)).msgParams.callee)
      (write_storage address key value)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_write_transient_storage:
  psf (λs. address = (FST (HD s.contexts)).msgParams.callee)
      (write_transient_storage address key value)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_update_accounts_increment_nonce:
  psf (λs. address = (FST (HD s.contexts)).msgParams.callee)
      (update_accounts (increment_nonce address))
Proof
  cheat  (* SCAFFOLD *)
QED

(* ---------------- Validation: step_sstore ---------------------- *)

Theorem psf_step_sstore:
  psf (λs. T) (step_sstore transient)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_sstore[simp]:
  preserves_same_frame (step_sstore transient)
Proof
  cheat  (* SCAFFOLD *)
QED

(* ---------------- Validation: abort_create_exists --------------- *)

Theorem psf_abort_create_exists_callee:
  psf (λs. senderAddress = (FST (HD s.contexts)).msgParams.callee)
      (abort_create_exists senderAddress)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem abort_create_exists_same_frame:
  s.contexts ≠ [] ∧
  senderAddress = (FST (HD s.contexts)).msgParams.callee ⇒
  same_frame_rel s (SND (abort_create_exists senderAddress s))
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_Mul[simp]:
  preserves_same_frame (step_inst Mul)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_Sub[simp]:
  preserves_same_frame (step_inst Sub)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_Div[simp]:
  preserves_same_frame (step_inst Div)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_SDiv[simp]:
  preserves_same_frame (step_inst SDiv)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_Mod[simp]:
  preserves_same_frame (step_inst Mod)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_SMod[simp]:
  preserves_same_frame (step_inst SMod)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_AddMod[simp]:
  preserves_same_frame (step_inst AddMod)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_MulMod[simp]:
  preserves_same_frame (step_inst MulMod)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_Exp[simp]:
  preserves_same_frame (step_inst Exp)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_SignExtend[simp]:
  preserves_same_frame (step_inst SignExtend)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_LT[simp]:
  preserves_same_frame (step_inst LT)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_GT[simp]:
  preserves_same_frame (step_inst GT)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_SLT[simp]:
  preserves_same_frame (step_inst SLT)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_SGT[simp]:
  preserves_same_frame (step_inst SGT)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_Eq[simp]:
  preserves_same_frame (step_inst Eq)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_IsZero[simp]:
  preserves_same_frame (step_inst IsZero)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_And[simp]:
  preserves_same_frame (step_inst And)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_Or[simp]:
  preserves_same_frame (step_inst Or)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_XOr[simp]:
  preserves_same_frame (step_inst XOr)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_Not[simp]:
  preserves_same_frame (step_inst Not)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_Byte[simp]:
  preserves_same_frame (step_inst Byte)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_ShL[simp]:
  preserves_same_frame (step_inst ShL)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_ShR[simp]:
  preserves_same_frame (step_inst ShR)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_SAR[simp]:
  preserves_same_frame (step_inst SAR)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_CLZ[simp]:
  preserves_same_frame (step_inst CLZ)
Proof
  cheat  (* SCAFFOLD *)
QED

(* --- Hashing / context / tx params --- *)

Theorem preserves_same_frame_step_inst_Keccak256[simp]:
  preserves_same_frame (step_inst Keccak256)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_Address[simp]:
  preserves_same_frame (step_inst Address)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_Balance[simp]:
  preserves_same_frame (step_inst Balance)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_Origin[simp]:
  preserves_same_frame (step_inst Origin)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_Caller[simp]:
  preserves_same_frame (step_inst Caller)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_CallValue[simp]:
  preserves_same_frame (step_inst CallValue)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_CallDataLoad[simp]:
  preserves_same_frame (step_inst CallDataLoad)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_CallDataSize[simp]:
  preserves_same_frame (step_inst CallDataSize)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_CallDataCopy[simp]:
  preserves_same_frame (step_inst CallDataCopy)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_CodeSize[simp]:
  preserves_same_frame (step_inst CodeSize)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_CodeCopy[simp]:
  preserves_same_frame (step_inst CodeCopy)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_GasPrice[simp]:
  preserves_same_frame (step_inst GasPrice)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_ExtCodeSize[simp]:
  preserves_same_frame (step_inst ExtCodeSize)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_ExtCodeCopy[simp]:
  preserves_same_frame (step_inst ExtCodeCopy)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_ReturnDataSize[simp]:
  preserves_same_frame (step_inst ReturnDataSize)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_ReturnDataCopy[simp]:
  preserves_same_frame (step_inst ReturnDataCopy)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_ExtCodeHash[simp]:
  preserves_same_frame (step_inst ExtCodeHash)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_BlockHash[simp]:
  preserves_same_frame (step_inst BlockHash)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_CoinBase[simp]:
  preserves_same_frame (step_inst CoinBase)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_TimeStamp[simp]:
  preserves_same_frame (step_inst TimeStamp)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_Number[simp]:
  preserves_same_frame (step_inst Number)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_PrevRandao[simp]:
  preserves_same_frame (step_inst PrevRandao)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_GasLimit[simp]:
  preserves_same_frame (step_inst GasLimit)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_ChainId[simp]:
  preserves_same_frame (step_inst ChainId)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_SelfBalance[simp]:
  preserves_same_frame (step_inst SelfBalance)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_BaseFee[simp]:
  preserves_same_frame (step_inst BaseFee)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_BlobHash[simp]:
  preserves_same_frame (step_inst BlobHash)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_BlobBaseFee[simp]:
  preserves_same_frame (step_inst BlobBaseFee)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_SlotNumber[simp]:
  preserves_same_frame (step_inst SlotNumber)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_DupN[simp]:
  preserves_same_frame (step_inst DupN)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_SwapN[simp]:
  preserves_same_frame (step_inst SwapN)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_Exchange[simp]:
  preserves_same_frame (step_inst Exchange)
Proof
  cheat  (* SCAFFOLD *)
QED

(* --- Stack and memory --- *)

Theorem preserves_same_frame_step_inst_Pop[simp]:
  preserves_same_frame (step_inst Pop)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_MLoad[simp]:
  preserves_same_frame (step_inst MLoad)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_MStore[simp]:
  preserves_same_frame (step_inst MStore)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_MStore8[simp]:
  preserves_same_frame (step_inst MStore8)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_MCopy[simp]:
  preserves_same_frame (step_inst MCopy)
Proof
  cheat  (* SCAFFOLD *)
QED

(* --- Storage and transient storage --- *)

Theorem preserves_same_frame_step_inst_SLoad[simp]:
  preserves_same_frame (step_inst SLoad)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_SStore[simp]:
  preserves_same_frame (step_inst SStore)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_TLoad[simp]:
  preserves_same_frame (step_inst TLoad)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_TStore[simp]:
  preserves_same_frame (step_inst TStore)
Proof
  cheat  (* SCAFFOLD *)
QED

(* --- Control flow --- *)

Theorem preserves_same_frame_step_inst_Jump[simp]:
  preserves_same_frame (step_inst Jump)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_JumpI[simp]:
  preserves_same_frame (step_inst JumpI)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_PC[simp]:
  preserves_same_frame (step_inst PC)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_MSize[simp]:
  preserves_same_frame (step_inst MSize)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_Gas[simp]:
  preserves_same_frame (step_inst Gas)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_JumpDest[simp]:
  preserves_same_frame (step_inst JumpDest)
Proof
  cheat  (* SCAFFOLD *)
QED

(* --- Push / Dup / Swap / Log (indexed) --- *)

Theorem preserves_same_frame_step_inst_Push[simp]:
  preserves_same_frame (step_inst (Push n ws))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_Dup[simp]:
  preserves_same_frame (step_inst (Dup n))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_Swap[simp]:
  preserves_same_frame (step_inst (Swap n))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_Log[simp]:
  preserves_same_frame (step_inst (Log n))
Proof
  cheat  (* SCAFFOLD *)
QED

(* --- Terminators (return INR but don't mutate state in ways that
       violate same_frame_rel). Stop, Return, Revert, Invalid. --- *)

Theorem preserves_same_frame_step_inst_Stop[simp]:
  preserves_same_frame (step_inst Stop)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_Return[simp]:
  preserves_same_frame (step_inst Return)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_Revert[simp]:
  preserves_same_frame (step_inst Revert)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_Invalid[simp]:
  preserves_same_frame (step_inst Invalid)
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

(* ================================================================ *)
(* Utility: preserves_same_frame / cp imply length preservation.     *)
(* ================================================================ *)

Theorem cp_imp_length_contexts_preserved:
  cp m /\ m s = (r,s') /\ s.contexts <> []
  ==> LENGTH s'.contexts = LENGTH s.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_imp_length_contexts_preserved:
  preserves_same_frame m /\ m s = (r,s') /\ s.contexts <> [] ==>
  LENGTH s'.contexts = LENGTH s.contexts
Proof
  cheat  (* SCAFFOLD *)
QED


(* ================================================================ *)
(* SELFDESTRUCT psf details.                                         *)
(*                                                                   *)
(* SELFDESTRUCT modifies balances (not storage/code/nonce) and may   *)
(* add an address to rollback.toDelete. Under the weakened           *)
(* `same_frame_rel` (balances are free), these are callee-local      *)
(* changes, so `step_self_destruct` is `preserves_same_frame`.       *)
(*                                                                   *)
(* This section is placed here (rather than in the SSTORE block      *)
(* above) because the primary consumer is the step_self_destruct     *)
(* psf proof and its opcode wrapper.                                 *)
(* ================================================================ *)

(* ---------------- transfer_value field preservation ------------- *)

Theorem transfer_value_preserves_storage:
  (lookup_account a (transfer_value from to amt accs)).storage =
  (lookup_account a accs).storage
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem transfer_value_preserves_code:
  (lookup_account a (transfer_value from to amt accs)).code =
  (lookup_account a accs).code
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem transfer_value_preserves_nonce:
  (lookup_account a (transfer_value from to amt accs)).nonce =
  (lookup_account a accs).nonce
Proof
  cheat  (* SCAFFOLD *)
QED

(* ---------------- SELFDESTRUCT primitive psf lemmas ------------- *)

(* transfer_value only changes balances, which are free in the
   weakened same_frame_rel. *)
Theorem psf_update_accounts_transfer_value:
  psf (λs. T) (update_accounts (transfer_value fromAddr toAddr amount))
Proof
  cheat  (* SCAFFOLD *)
QED

(* add_to_delete appends to toDelete, which is free in the weakened
   relation. *)
Theorem psf_add_to_delete:
  psf (λs. T) (add_to_delete a)
Proof
  cheat  (* SCAFFOLD *)
QED

(* ---------------- psf step_self_destruct ----------------------- *)

(* step_self_destruct, line by line:
     pop_stack 1                    -- preserves_same_frame
     access_address address         -- preserves_same_frame
     senderAddress <- get_callee;
     set_return_data []             -- preserves_same_frame
     accounts <- get_accounts;
     consume_gas ...                -- preserves_same_frame
     assert_not_static              -- preserves_same_frame
     update_accounts (transfer_value senderAddress address balance)
                                    -- psf_update_accounts_transfer_value
     original <- get_original;
     if account_empty originalContract then
       add_to_delete senderAddress  -- psf_add_to_delete
     else return ()                 -- psf_return
     finish                         -- preserves_same_frame *)

Theorem psf_step_self_destruct:
  psf (λs. T) step_self_destruct
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_self_destruct[simp]:
  preserves_same_frame step_self_destruct
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_same_frame_step_inst_SelfDestruct[simp]:
  preserves_same_frame (step_inst SelfDestruct)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Aggregate: any non-call opcode preserves the frame. Dispatches via
   the per-opcode [simp]-tagged theorems above. *)
Theorem preserves_same_frame_step_inst_not_call:
  ¬is_call op ⇒ preserves_same_frame (step_inst op)
Proof
  cheat  (* SCAFFOLD *)
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
  LENGTH s'.contexts = LENGTH s.contexts + 1
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_create_length:
  s.contexts ≠ [] ∧
  proceed_create senderAddr addr value code gas s = (r, s') ⇒
  LENGTH s'.contexts = LENGTH s.contexts + 1
Proof
  cheat  (* SCAFFOLD *)
QED

(* ================================================================== *)
(* Stage 2: Implication bridges from same_frame_rel.                  *)
(*                                                                    *)
(* IMPORTANT: same_frame_rel does NOT imply rollback_rel or cp_rel,    *)
(* because callee_local_changes allows the callee's storage, code,    *)
(* and nonce to change, and any account's balance to change. cp_rel    *)
(* requires full rollback equality, which is strictly stronger.        *)
(*                                                                    *)
(* What same_frame_rel DOES imply:                                    *)
(*   - access monotonicity (addresses and storageKeys subsets)        *)
(*   - non-callee accounts: storage, code, nonce preserved             *)
(*   - msdomain_compatible                                            *)
(*   - txParams equality                                              *)
(* These bridges live in vfmStoragePredicates (for access_monotone)   *)
(* and here (for cp_rel and non-callee preservation).                 *)
(* ================================================================== *)

(* same_frame_rel implies that the head's callee has its storage,    *)
(* code, and nonce possibly changed, but non-callee accounts are     *)
(* preserved in storage/code/nonce. This is the callee_local_changes  *)
(* component extracted as a relation.                                *)
Definition non_callee_storage_rel_def:
  non_callee_storage_rel callee s s' ⇔
    ∀a. a ≠ callee ⇒
      (lookup_account a s'.rollback.accounts).storage =
      (lookup_account a s.rollback.accounts).storage ∧
      (lookup_account a s'.rollback.accounts).code =
      (lookup_account a s.rollback.accounts).code ∧
      (lookup_account a s'.rollback.accounts).nonce =
      (lookup_account a s.rollback.accounts).nonce
End

Theorem same_frame_rel_imp_non_callee_storage_rel:
  same_frame_rel s s' ⇒
  non_callee_storage_rel (FST (HD s.contexts)).msgParams.callee s s'
Proof
  cheat  (* SCAFFOLD *)
QED

(* same_frame_rel implies txParams equality. *)
Theorem same_frame_rel_imp_txParams_rel:
  same_frame_rel s s' ⇒ s'.txParams = s.txParams
Proof
  cheat  (* SCAFFOLD *)
QED

(* same_frame_rel implies msdomain_compatible. *)
Theorem same_frame_rel_imp_msdomain_compatible:
  same_frame_rel s s' ⇒ msdomain_compatible s.msdomain s'.msdomain
Proof
  cheat  (* SCAFFOLD *)
QED

(* Bridge: preserves same_frame_rel implies preserves                   *)
(* non_callee_storage_rel (when contexts ≠ []).                        *)
Theorem preserves_same_frame_imp_preserves_non_callee_storage:
  preserves same_frame_rel m ⇒
  preserves (λs s'. s.contexts ≠ [] ⇒
    non_callee_storage_rel (FST (HD s.contexts)).msgParams.callee s s') m
Proof
  cheat  (* SCAFFOLD *)
QED

(* Bridge: preserves same_frame_rel implies preserves txParams_rel.     *)
Theorem preserves_same_frame_imp_preserves_txParams:
  preserves same_frame_rel m ⇒ preserves (λs s'. s'.txParams = s.txParams) m
Proof
  cheat  (* SCAFFOLD *)
QED

(* Bridge: preserves same_frame_rel implies preserves                   *)
(* msdomain_compatible.                                               *)
Theorem preserves_same_frame_imp_preserves_msdomain_compatible:
  preserves same_frame_rel m ⇒
  preserves (λs s'. msdomain_compatible s.msdomain s'.msdomain) m
Proof
  cheat  (* SCAFFOLD *)
QED
