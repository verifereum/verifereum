(*
 * jumpDest preservation through VFM execution.
 *
 * Only step_jump and step_jumpi modify the jumpDest field of the current
 * context. All other operations preserve it. This is proved compositionally:
 * monad combinators preserve the property, leaf operations trivially preserve
 * it, and all non-Jump/JumpI opcodes inherit it.
 *
 * Main exported theorem:
 *   step_inst_non_jump_preserves_jumpDest:
 *     step_inst op s = (r, s') ∧ s.contexts ≠ [] ∧ s'.contexts ≠ [] ∧
 *     ¬is_call op ∧ op ≠ Jump ∧ op ≠ JumpI ⇒
 *     (FST (HD s'.contexts)).jumpDest = (FST (HD s.contexts)).jumpDest
 *)
Theory vfmJumpDest
Ancestors
  combin pair list
  vfmExecution vfmExecutionProp vfmContext vfmSameFrame
  vfmHandleStep vfmStepLength vfmPreserves
Libs
  BasicProvers

val _ = Parse.hide "add"

(* ================================================================ *)
(* Definition                                                        *)
(* ================================================================ *)

Definition preserves_jumpDest_def:
  preserves_jumpDest m ⇔
    ∀s r s'. m s = ((r:α + exception option), s') ∧
             s.contexts ≠ [] ⇒ s'.contexts ≠ [] ∧
      (FST (HD s'.contexts)).jumpDest = (FST (HD s.contexts)).jumpDest
End

(* ================================================================== *)
(* jumpDest_rel: the state relation underlying preserves_jumpDest.      *)
(*                                                                    *)
(* When s.contexts ≠ [], jumpDest_rel preserves the head context's    *)
(* jumpDest and ensures contexts remain non-empty. When s.contexts    *)
(* = [], only the non-emptiness of s'.contexts is required (the       *)
(* jumpDest equality is vacuously true).                              *)
(* ================================================================== *)

Definition jumpDest_rel_def:
  jumpDest_rel s s' ⇔
    s'.contexts ≠ [] ∧
    (s.contexts ≠ [] ⇒
      (FST (HD s'.contexts)).jumpDest = (FST (HD s.contexts)).jumpDest)
End

Theorem preserves_jumpDest_eq_preserves_when:
  preserves_jumpDest m ⇔ preserves_when (λs. s.contexts ≠ []) jumpDest_rel m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem jumpDest_rel_refl:
  s.contexts ≠ [] ⇒ jumpDest_rel s s
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem jumpDest_rel_trans:
  jumpDest_rel s1 s2 ∧ jumpDest_rel s2 s3 ⇒ jumpDest_rel s1 s3
Proof
  cheat  (* SCAFFOLD *)
QED

(* jumpDest_rel preserves non-empty contexts (precondition transfer).  *)
Theorem jumpDest_rel_contexts_ne:
  s.contexts ≠ [] ∧ jumpDest_rel s s' ⇒ s'.contexts ≠ []
Proof
  cheat  (* SCAFFOLD *)
QED

(* ================================================================ *)
(* all_jumpDest_NONE: strengthened property for full stack          *)
(* ================================================================ *)

Definition all_jumpDest_NONE_def:
  all_jumpDest_NONE s ⇔ EVERY (λc. (FST c).jumpDest = NONE) s.contexts
End

Definition preserves_all_jumpDest_NONE_def:
  preserves_all_jumpDest_NONE m ⇔
    ∀s r s'. m s = (r, s') ∧ all_jumpDest_NONE s ⇒ all_jumpDest_NONE s'
End

(* Bridge lemma: primitives that preserve jumpDest and don't change
   contexts structure also preserve all_jumpDest_NONE *)
Theorem preserves_jumpDest_same_contexts_imp_all:
  preserves_jumpDest m ∧
  (∀s r s'. m s = (r, s') ⇒ s'.contexts = s.contexts) ⇒
  preserves_all_jumpDest_NONE m
Proof
  cheat  (* SCAFFOLD *)
QED

(* Bridge lemma: use existing preserves_jumpDest and preserves_same_frame.
   The extra condition handles the empty contexts case. *)
Theorem preserves_jumpDest_and_same_frame_imp_all:
  preserves_jumpDest m ∧ preserves_same_frame m ∧
  (∀s r s'. m s = (r, s') ∧ s.contexts = [] ⇒ s'.contexts = []) ⇒
  preserves_all_jumpDest_NONE m
Proof
  cheat  (* SCAFFOLD *)
QED

(* Combinator lemmas for preserves_all_jumpDest_NONE *)
Theorem preserves_all_jumpDest_NONE_bind[simp]:
  preserves_all_jumpDest_NONE g ∧ (∀x. preserves_all_jumpDest_NONE (f x)) ⇒
  preserves_all_jumpDest_NONE (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_ignore_bind[simp]:
  preserves_all_jumpDest_NONE g ∧ preserves_all_jumpDest_NONE f ⇒
  preserves_all_jumpDest_NONE (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_handle[simp]:
  preserves_all_jumpDest_NONE f ∧ (∀e. preserves_all_jumpDest_NONE (h e)) ⇒
  preserves_all_jumpDest_NONE (handle f h)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Leaf operations for preserves_all_jumpDest_NONE *)
Theorem preserves_all_jumpDest_NONE_return[simp]:
  preserves_all_jumpDest_NONE (return x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_fail[simp]:
  preserves_all_jumpDest_NONE (fail e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_assert[simp]:
  preserves_all_jumpDest_NONE (assert b e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_finish[simp]:
  preserves_all_jumpDest_NONE finish
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_revert[simp]:
  preserves_all_jumpDest_NONE revert
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_reraise[simp]:
  preserves_all_jumpDest_NONE (reraise e)
Proof
  cheat  (* SCAFFOLD *)
QED

(* State-reading operations that don't change contexts *)
Theorem preserves_all_jumpDest_NONE_get_current_context[simp]:
  preserves_all_jumpDest_NONE get_current_context
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_get_gas_left[simp]:
  preserves_all_jumpDest_NONE get_gas_left
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_get_callee[simp]:
  preserves_all_jumpDest_NONE get_callee
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_get_accounts[simp]:
  preserves_all_jumpDest_NONE get_accounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_get_rollback[simp]:
  preserves_all_jumpDest_NONE get_rollback
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_get_static[simp]:
  preserves_all_jumpDest_NONE get_static
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_get_num_contexts[simp]:
  preserves_all_jumpDest_NONE get_num_contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_get_original[simp]:
  preserves_all_jumpDest_NONE get_original
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_get_tx_params[simp]:
  preserves_all_jumpDest_NONE get_tx_params
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_get_tStorage[simp]:
  preserves_all_jumpDest_NONE get_tStorage
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_get_call_data[simp]:
  preserves_all_jumpDest_NONE get_call_data
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_get_return_data[simp]:
  preserves_all_jumpDest_NONE get_return_data
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_get_current_code[simp]:
  preserves_all_jumpDest_NONE get_current_code
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_get_output_to[simp]:
  preserves_all_jumpDest_NONE get_output_to
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_get_value[simp]:
  preserves_all_jumpDest_NONE get_value
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_get_caller[simp]:
  preserves_all_jumpDest_NONE get_caller
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_get_return_data_check[simp]:
  preserves_all_jumpDest_NONE (get_return_data_check off sz)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_get_code[simp]:
  preserves_all_jumpDest_NONE (get_code a)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_memory_expansion_info[simp]:
  preserves_all_jumpDest_NONE (memory_expansion_info off len)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Operations that modify rollback/domain but not contexts *)
Theorem preserves_all_jumpDest_NONE_set_rollback[simp]:
  preserves_all_jumpDest_NONE (set_rollback rb)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_update_accounts[simp]:
  preserves_all_jumpDest_NONE (update_accounts f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_set_domain[simp]:
  preserves_all_jumpDest_NONE (set_domain d)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_set_tStorage[simp]:
  preserves_all_jumpDest_NONE (set_tStorage x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_add_to_delete[simp]:
  preserves_all_jumpDest_NONE (add_to_delete a)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Operations that modify current context but keep jumpDest = NONE *)
Theorem preserves_all_jumpDest_NONE_set_current_context_jumpDest_NONE:
  (∀c. (f c).jumpDest = NONE) ⇒
  preserves_all_jumpDest_NONE (bind get_current_context (λc. set_current_context (f c)))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_pop_stack[simp]:
  preserves_all_jumpDest_NONE (pop_stack n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_push_stack[simp]:
  preserves_all_jumpDest_NONE (push_stack ws)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_consume_gas[simp]:
  preserves_all_jumpDest_NONE (consume_gas g)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_unuse_gas[simp]:
  preserves_all_jumpDest_NONE (unuse_gas g)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_set_return_data[simp]:
  preserves_all_jumpDest_NONE (set_return_data rd)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_push_logs[simp]:
  preserves_all_jumpDest_NONE (push_logs ls)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_update_gas_refund[simp]:
  preserves_all_jumpDest_NONE (update_gas_refund (a, sb))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_update_gas_refund_any[simp]:
  preserves_all_jumpDest_NONE (update_gas_refund updates)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_expand_memory[simp]:
  preserves_all_jumpDest_NONE (expand_memory n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_write_memory[simp]:
  preserves_all_jumpDest_NONE (write_memory off bytes)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_read_memory[simp]:
  preserves_all_jumpDest_NONE (read_memory off len)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_access_address[simp]:
  preserves_all_jumpDest_NONE (access_address a)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_access_slot[simp]:
  preserves_all_jumpDest_NONE (access_slot sk)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_assert_not_static[simp]:
  preserves_all_jumpDest_NONE assert_not_static
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_ensure_storage_in_domain[simp]:
  preserves_all_jumpDest_NONE (ensure_storage_in_domain a)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_write_storage[simp]:
  preserves_all_jumpDest_NONE (write_storage a k v)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_write_transient_storage[simp]:
  preserves_all_jumpDest_NONE (write_transient_storage a k v)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_set_original[simp]:
  preserves_all_jumpDest_NONE (set_original orig)
Proof
  cheat  (* SCAFFOLD *)
QED

(* inc_pc sets jumpDest := NONE explicitly, preserving all_jumpDest_NONE *)
Theorem preserves_all_jumpDest_NONE_inc_pc[simp]:
  preserves_all_jumpDest_NONE inc_pc
Proof
  cheat  (* SCAFFOLD *)
QED

(* push_context: new context has jumpDest = NONE from initial_context *)
Theorem preserves_all_jumpDest_NONE_push_context[simp]:
  (FST ctx).jumpDest = NONE ⇒
  preserves_all_jumpDest_NONE (push_context ctx)
Proof
  cheat  (* SCAFFOLD *)
QED

(* pop_context: removes head, tail still all NONE *)
Theorem preserves_all_jumpDest_NONE_pop_context[simp]:
  preserves_all_jumpDest_NONE pop_context
Proof
  cheat  (* SCAFFOLD *)
QED

(* Tactic for preserves_all_jumpDest_NONE proofs *)
val pajdn_tac = rpt (
  (irule preserves_all_jumpDest_NONE_bind >> rw[]) ORELSE
  (irule preserves_all_jumpDest_NONE_ignore_bind >> rw[]) ORELSE
  (irule preserves_all_jumpDest_NONE_handle >> rw[])
)

(* Abort functions preserve all_jumpDest_NONE *)
Theorem preserves_all_jumpDest_NONE_abort_call_value[simp]:
  preserves_all_jumpDest_NONE (abort_call_value x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_abort_unuse[simp]:
  preserves_all_jumpDest_NONE (abort_unuse x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_abort_create_exists[simp]:
  preserves_all_jumpDest_NONE (abort_create_exists a)
Proof
  cheat  (* SCAFFOLD *)
QED

(* handle_create preserves all_jumpDest_NONE *)
Theorem preserves_all_jumpDest_NONE_handle_create[simp]:
  preserves_all_jumpDest_NONE (handle_create e)
Proof
  cheat  (* SCAFFOLD *)
QED

(* pop_and_incorporate_context preserves all_jumpDest_NONE *)
Theorem preserves_all_jumpDest_NONE_pop_and_incorporate_context[simp]:
  preserves_all_jumpDest_NONE (pop_and_incorporate_context b)
Proof
  cheat  (* SCAFFOLD *)
QED

(* handle_exception preserves all_jumpDest_NONE *)
Theorem preserves_all_jumpDest_NONE_handle_exception[simp]:
  preserves_all_jumpDest_NONE (handle_exception e)
Proof
  cheat  (* SCAFFOLD *)
QED

(* inc_pc_or_jump: either increments pc (preserves) or jumps and sets jumpDest := NONE *)
Theorem preserves_all_jumpDest_NONE_inc_pc_or_jump[simp]:
  preserves_all_jumpDest_NONE (inc_pc_or_jump op)
Proof
  cheat  (* SCAFFOLD *)
QED

(* inc_pc_or_jump INL establishes all_jumpDest_NONE given only TL has jumpDest NONE *)
Theorem inc_pc_or_jump_INL_establishes_all_jumpDest_NONE:
  inc_pc_or_jump op s = (INL (), s') ∧ ¬is_call op ∧ s.contexts ≠ [] ∧
  EVERY (λc. (FST c).jumpDest = NONE) (TL s.contexts) ⇒
  all_jumpDest_NONE s'
Proof
  cheat  (* SCAFFOLD *)
QED

(* Jump/JumpI + inc_pc_or_jump INL preserves all_jumpDest_NONE *)
Theorem step_jump_inc_pc_INL_preserves_all_jumpDest_NONE:
  (do step_inst Jump; inc_pc_or_jump Jump od) s = (INL x, s') ∧
  all_jumpDest_NONE s ⇒ all_jumpDest_NONE s'
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_jumpi_inc_pc_INL_preserves_all_jumpDest_NONE:
  (do step_inst JumpI; inc_pc_or_jump JumpI od) s = (INL (), s') ∧
  all_jumpDest_NONE s ⇒ all_jumpDest_NONE s'
Proof
  cheat  (* SCAFFOLD *)
QED

(* ================================================================ *)
(* Layer 1: Monad combinator preservation rules                     *)
(* ================================================================ *)

Theorem preserves_jumpDest_bind[simp]:
  preserves_jumpDest g ∧ (∀x. preserves_jumpDest (f x)) ⇒
  preserves_jumpDest (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_ignore_bind[simp]:
  preserves_jumpDest g ∧ preserves_jumpDest f ⇒
  preserves_jumpDest (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_handle[simp]:
  preserves_jumpDest f ∧ (∀e. preserves_jumpDest (h e)) ⇒
  preserves_jumpDest (handle f h)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_cond[simp]:
  preserves_jumpDest m1 ∧ preserves_jumpDest m2 ⇒
  preserves_jumpDest (if b then m1 else m2)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_case_option[simp]:
  preserves_jumpDest m_none ∧ (∀x. preserves_jumpDest (m_some x)) ⇒
  preserves_jumpDest (case opt of NONE => m_none | SOME x => m_some x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_case_sum[simp]:
  (∀x. preserves_jumpDest (f x)) ∧ (∀y. preserves_jumpDest (g y)) ⇒
  preserves_jumpDest (case s of INL x => f x | INR y => g y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_case_pair[simp]:
  (∀x y. preserves_jumpDest (f x y)) ⇒
  preserves_jumpDest (case p of (x, y) => f x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_let[simp]:
  (∀x. preserves_jumpDest (f x)) ⇒
  preserves_jumpDest (let x = v in f x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_uncurry[simp]:
  (∀x y. preserves_jumpDest (f x y)) ⇒
  preserves_jumpDest (UNCURRY f p)
Proof
  cheat  (* SCAFFOLD *)
QED

(* ================================================================ *)
(* Layer 2: Leaf / primitive operations                             *)
(* ================================================================ *)

Theorem preserves_jumpDest_return[simp]:
  preserves_jumpDest (return x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_fail[simp]:
  preserves_jumpDest (fail e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_assert[simp]:
  preserves_jumpDest (assert b e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_finish[simp]:
  preserves_jumpDest finish
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_revert[simp]:
  preserves_jumpDest revert
Proof
  cheat  (* SCAFFOLD *)
QED

(* ================================================================ *)
(* Layer 3: State-accessing primitives that don't touch jumpDest    *)
(* ================================================================ *)

(* Operations that only read state *)
Theorem preserves_jumpDest_get_current_context[simp]:
  preserves_jumpDest get_current_context
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_get_gas_left[simp]:
  preserves_jumpDest get_gas_left
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_get_callee[simp]:
  preserves_jumpDest get_callee
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_get_accounts[simp]:
  preserves_jumpDest get_accounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_get_rollback[simp]:
  preserves_jumpDest get_rollback
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_get_static[simp]:
  preserves_jumpDest get_static
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_get_num_contexts[simp]:
  preserves_jumpDest get_num_contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_get_original[simp]:
  preserves_jumpDest get_original
Proof
  cheat  (* SCAFFOLD *)
QED

(* Operations that modify rollback but not contexts *)
Theorem preserves_jumpDest_set_rollback[simp]:
  preserves_jumpDest (set_rollback rb)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_update_accounts[simp]:
  preserves_jumpDest (update_accounts f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_set_original[simp]:
  preserves_jumpDest (set_original orig)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_set_domain[simp]:
  preserves_jumpDest (set_domain d)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Operations that modify context fields OTHER than jumpDest *)

(* Key lemma: set_current_context preserves jumpDest if the new context has same jumpDest *)
Theorem preserves_jumpDest_set_current_context_if:
  (∀c. (f c).jumpDest = c.jumpDest) ⇒
  preserves_jumpDest (bind get_current_context (λc. set_current_context (f c)))
Proof
  cheat  (* SCAFFOLD *)
QED

(* Most context-modifying ops use a pattern like:
   context <- get_current_context;
   set_current_context $ context with <field> := <value>
   where <field> ≠ jumpDest. We capture this with a specialized lemma. *)

Theorem preserves_jumpDest_update_context_field:
  (∀c. (f c).jumpDest = c.jumpDest) ⇒
  preserves_jumpDest (bind get_current_context (λc. set_current_context (f c)))
Proof
  cheat  (* SCAFFOLD *)
QED

(* Derived: pop_stack preserves jumpDest *)
Theorem preserves_jumpDest_pop_stack[simp]:
  preserves_jumpDest (pop_stack n)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Derived: push_stack preserves jumpDest *)
Theorem preserves_jumpDest_push_stack[simp]:
  preserves_jumpDest (push_stack ws)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Derived: consume_gas preserves jumpDest *)
Theorem preserves_jumpDest_consume_gas[simp]:
  preserves_jumpDest (consume_gas g)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Derived: unuse_gas preserves jumpDest *)
Theorem preserves_jumpDest_unuse_gas[simp]:
  preserves_jumpDest (unuse_gas g)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Derived: set_return_data preserves jumpDest *)
Theorem preserves_jumpDest_set_return_data[simp]:
  preserves_jumpDest (set_return_data rd)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Derived: push_logs preserves jumpDest *)
Theorem preserves_jumpDest_push_logs[simp]:
  preserves_jumpDest (push_logs ls)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Derived: update_gas_refund preserves jumpDest *)
Theorem preserves_jumpDest_update_gas_refund[simp]:
  preserves_jumpDest (update_gas_refund (a, sb))
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_update_gas_refund_any[simp]:
  preserves_jumpDest (update_gas_refund updates)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Derived: expand_memory preserves jumpDest *)
Theorem preserves_jumpDest_expand_memory[simp]:
  preserves_jumpDest (expand_memory n)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Derived: write_memory preserves jumpDest *)
Theorem preserves_jumpDest_write_memory[simp]:
  preserves_jumpDest (write_memory off bytes)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Derived: read_memory preserves jumpDest *)
Theorem preserves_jumpDest_read_memory[simp]:
  preserves_jumpDest (read_memory off len)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Derived: memory_expansion_info preserves jumpDest *)
Theorem preserves_jumpDest_memory_expansion_info[simp]:
  preserves_jumpDest (memory_expansion_info off len)
Proof
  cheat  (* SCAFFOLD *)
QED

(* domain_check preserves jumpDest when cont does *)
Theorem preserves_jumpDest_domain_check[simp]:
  preserves_jumpDest cont ⇒
  preserves_jumpDest (domain_check err check add cont)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Derived: access_address preserves jumpDest *)
Theorem preserves_jumpDest_access_address[simp]:
  preserves_jumpDest (access_address a)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Derived: access_slot preserves jumpDest *)
Theorem preserves_jumpDest_access_slot[simp]:
  preserves_jumpDest (access_slot sk)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Derived: assert_not_static preserves jumpDest *)
Theorem preserves_jumpDest_assert_not_static[simp]:
  preserves_jumpDest assert_not_static
Proof
  cheat  (* SCAFFOLD *)
QED

(* Derived: ensure_storage_in_domain preserves jumpDest *)
Theorem preserves_jumpDest_ensure_storage_in_domain[simp]:
  preserves_jumpDest (ensure_storage_in_domain a)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Derived: write_storage preserves jumpDest *)
Theorem preserves_jumpDest_write_storage[simp]:
  preserves_jumpDest (write_storage a k v)
Proof
  cheat  (* SCAFFOLD *)
QED

(* More primitives needed for step_* functions *)
Theorem preserves_jumpDest_get_tx_params[simp]:
  preserves_jumpDest get_tx_params
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_get_tStorage[simp]:
  preserves_jumpDest get_tStorage
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_set_tStorage[simp]:
  preserves_jumpDest (set_tStorage x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_write_transient_storage[simp]:
  preserves_jumpDest (write_transient_storage a k v)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_add_to_delete[simp]:
  preserves_jumpDest (add_to_delete a)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_get_call_data[simp]:
  preserves_jumpDest get_call_data
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_get_return_data[simp]:
  preserves_jumpDest get_return_data
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_get_current_code[simp]:
  preserves_jumpDest get_current_code
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_get_output_to[simp]:
  preserves_jumpDest get_output_to
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_get_return_data_check[simp]:
  preserves_jumpDest (get_return_data_check off sz)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_get_code[simp]:
  preserves_jumpDest (get_code a)
Proof
  cheat  (* SCAFFOLD *)
QED

(* ================================================================ *)
(* Layer 4: Step helper functions                                   *)
(* ================================================================ *)

(* Tactic: repeatedly decompose through bind/ignore_bind *)
val pjd_tac = rpt (
  (irule preserves_jumpDest_bind >> rw[]) ORELSE
  (irule preserves_jumpDest_ignore_bind >> rw[]) ORELSE
  (irule preserves_jumpDest_handle >> rw[])
)

Theorem preserves_jumpDest_step_binop[simp]:
  preserves_jumpDest (step_binop op f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_monop[simp]:
  preserves_jumpDest (step_monop op f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_modop[simp]:
  preserves_jumpDest (step_modop op f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_context[simp]:
  preserves_jumpDest (step_context op f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_msgParams[simp]:
  preserves_jumpDest (step_msgParams op f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_txParams[simp]:
  preserves_jumpDest (step_txParams op f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_exp[simp]:
  preserves_jumpDest step_exp
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_keccak256[simp]:
  preserves_jumpDest step_keccak256
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_balance[simp]:
  preserves_jumpDest step_balance
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_call_data_load[simp]:
  preserves_jumpDest step_call_data_load
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_copy_to_memory[simp]:
  (∀f. src = SOME f ⇒ preserves_jumpDest f) ⇒
  preserves_jumpDest (copy_to_memory g off srcoff sz src)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_copy_to_memory[simp]:
  (∀f. src = SOME f ⇒ preserves_jumpDest f) ⇒
  preserves_jumpDest (step_copy_to_memory op src)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_return_data_copy[simp]:
  preserves_jumpDest step_return_data_copy
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_ext_code_size[simp]:
  preserves_jumpDest step_ext_code_size
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_ext_code_copy[simp]:
  preserves_jumpDest step_ext_code_copy
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_ext_code_hash[simp]:
  preserves_jumpDest step_ext_code_hash
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_block_hash[simp]:
  preserves_jumpDest step_block_hash
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_blob_hash[simp]:
  preserves_jumpDest step_blob_hash
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_self_balance[simp]:
  preserves_jumpDest step_self_balance
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_pop[simp]:
  preserves_jumpDest step_pop
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_mload[simp]:
  preserves_jumpDest step_mload
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_mstore[simp]:
  preserves_jumpDest (step_mstore op)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_sload[simp]:
  preserves_jumpDest (step_sload b)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_sstore_gas_consumption[simp]:
  preserves_jumpDest (step_sstore_gas_consumption a k v)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_sstore[simp]:
  preserves_jumpDest (step_sstore b)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_push[simp]:
  preserves_jumpDest (step_push n ws)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_dup[simp]:
  preserves_jumpDest (step_dup n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_swap[simp]:
  preserves_jumpDest (step_swap n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_dupn[simp]:
  preserves_jumpDest step_dupn
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_swapn[simp]:
  preserves_jumpDest step_swapn
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_exchange[simp]:
  preserves_jumpDest step_exchange
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_log[simp]:
  preserves_jumpDest (step_log n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_return[simp]:
  preserves_jumpDest (step_return b)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_step_self_destruct[simp]:
  preserves_jumpDest step_self_destruct
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_inc_pc[simp]:
  preserves_jumpDest (inc_pc)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_abort_call_value[simp]:
  preserves_jumpDest (abort_call_value x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_abort_unuse[simp]:
  preserves_jumpDest (abort_unuse x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_get_value[simp]:
  preserves_jumpDest get_value
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_get_caller[simp]:
  preserves_jumpDest get_caller
Proof
  cheat  (* SCAFFOLD *)
QED

(* ================================================================ *)
(* Precompiles                                                       *)
(* ================================================================ *)

Theorem preserves_jumpDest_precompile_ecrecover[simp]:
  preserves_jumpDest precompile_ecrecover
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_precompile_identity[simp]:
  preserves_jumpDest precompile_identity
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_precompile_modexp[simp]:
  preserves_jumpDest precompile_modexp
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_precompile_sha2_256[simp]:
  preserves_jumpDest precompile_sha2_256
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_precompile_ripemd_160[simp]:
  preserves_jumpDest precompile_ripemd_160
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_precompile_ecadd[simp]:
  preserves_jumpDest precompile_ecadd
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_precompile_ecmul[simp]:
  preserves_jumpDest precompile_ecmul
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_precompile_ecpairing[simp]:
  preserves_jumpDest precompile_ecpairing
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_precompile_blake2f[simp]:
  preserves_jumpDest precompile_blake2f
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_precompile_point_eval[simp]:
  preserves_jumpDest precompile_point_eval
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_precompile_bls_g1add[simp]:
  preserves_jumpDest precompile_bls_g1add
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_precompile_bls_g1msm[simp]:
  preserves_jumpDest precompile_bls_g1msm
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_precompile_bls_g2add[simp]:
  preserves_jumpDest precompile_bls_g2add
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_precompile_bls_g2msm[simp]:
  preserves_jumpDest precompile_bls_g2msm
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_precompile_bls_pairing[simp]:
  preserves_jumpDest precompile_bls_pairing
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_precompile_bls_map_fp_to_g1[simp]:
  preserves_jumpDest precompile_bls_map_fp_to_g1
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_precompile_bls_map_fp2_to_g2[simp]:
  preserves_jumpDest precompile_bls_map_fp2_to_g2
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_precompile_p256verify[simp]:
  preserves_jumpDest precompile_p256verify
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_dispatch_precompiles[simp]:
  preserves_jumpDest (dispatch_precompiles a)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem bind_preserves_jumpDest_imp:
  bind g f s = (r,s') ∧
  preserves_jumpDest g ∧
  s.contexts ≠ [] ∧
  (∀x s. f x s = (r, s') ∧ s.contexts ≠ [] ⇒
              s'.contexts ≠ [] ∧
              (FST(HD s'.contexts)).jumpDest =
              (FST(HD s.contexts)).jumpDest)
  ⇒
  s'.contexts ≠ [] ∧
  (FST(HD s'.contexts)).jumpDest =
  (FST(HD s.contexts)).jumpDest
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem bind_preserves_jumpDest_NONE_imp:
  bind g f s = (r,s') ∧
  preserves_jumpDest g ∧
  (FST(HD s.contexts)).jumpDest = NONE ∧
  s.contexts ≠ [] ∧
  (∀x s. f x s = (r, s') ∧ s.contexts ≠ [] ∧
         (FST(HD s.contexts)).jumpDest = NONE ⇒
              s'.contexts ≠ [] ∧
              (FST(HD s'.contexts)).jumpDest = NONE)
  ⇒
  s'.contexts ≠ [] ∧
  (FST(HD s'.contexts)).jumpDest = NONE
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_NONE_proceed_call:
  proceed_call op a b c d e f g h s = (x, s') ∧ s.contexts ≠ [] ∧
  (FST(HD s.contexts)).jumpDest = NONE
  ⇒
  s'.contexts ≠ [] ∧
  (FST(HD s'.contexts)).jumpDest = NONE
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_NONE_step_call:
  step_call op s = (x, s') ∧ s.contexts ≠ [] ∧
  (FST (HD s.contexts)).jumpDest = NONE
  ⇒
  s'.contexts ≠ [] ∧
  (FST (HD s'.contexts)).jumpDest = NONE
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_abort_create_exists[simp]:
  preserves_jumpDest (abort_create_exists a)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_NONE_proceed_create:
  proceed_create a b c d e s = (x, s') ∧ s.contexts ≠ [] ∧
  (FST(HD s.contexts)).jumpDest = NONE
  ⇒
  s'.contexts ≠ [] ∧
  (FST(HD s'.contexts)).jumpDest = NONE
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_NONE_step_create:
  step_create two s = (x, s') ∧ s.contexts ≠ [] ∧
  (FST (HD s.contexts)).jumpDest = NONE
  ⇒
  s'.contexts ≠ [] ∧
  (FST (HD s'.contexts)).jumpDest = NONE
Proof
  cheat  (* SCAFFOLD *)
QED

(* ================================================================ *)
(* Main theorem: non-Jump/JumpI step_inst preserves jumpDest        *)
(* ================================================================ *)

(* The proof works by case analysis on the opcode. For each non-Jump/JumpI
   opcode, step_inst expands to a combination of the primitives we've
   proved preserve jumpDest. *)
Theorem step_inst_non_jump_preserves_jumpDest:
  step_inst op s = (r, s') ∧ s.contexts ≠ [] ∧ s'.contexts ≠ [] ∧
  ¬is_call op ∧ op ≠ Jump ∧ op ≠ JumpI ⇒
  (FST (HD s'.contexts)).jumpDest = (FST (HD s.contexts)).jumpDest
Proof
  cheat  (* SCAFFOLD *)
QED

(* Contrapositive form useful for the main application *)
Theorem step_inst_jumpDest_changed_imp_jump:
  step_inst op s = (r, s') ∧ s.contexts ≠ [] ∧ s'.contexts ≠ [] ∧ ¬is_call op ∧
  (FST (HD s'.contexts)).jumpDest ≠ (FST (HD s.contexts)).jumpDest ⇒
  op = Jump ∨ op = JumpI
Proof
  cheat  (* SCAFFOLD *)
QED

(* Specialized form: if jumpDest is SOME after step_inst and was NONE before,
   then op = Jump or JumpI *)
Theorem step_inst_jumpDest_NONE_to_SOME_imp_jump:
  step_inst op s = (r, s') ∧ s.contexts ≠ [] ∧ s'.contexts ≠ [] ∧ ¬is_call op ∧
  (FST (HD s.contexts)).jumpDest = NONE ∧
  (FST (HD s'.contexts)).jumpDest = SOME pc ⇒
  op = Jump ∨ op = JumpI
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inst_Stop_preserves_jumpDest:
  preserves_jumpDest (step_inst Stop)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inst_Invalid_preserves_jumpDest:
  preserves_jumpDest (step_inst Invalid)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_reraise[simp]:
  preserves_jumpDest (reraise e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_jumpDest_handle_create[simp]:
  preserves_jumpDest (handle_create e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inc_pc_or_jump_INL_jumpDest_NONE:
  inc_pc_or_jump op s = (INL x, s') ∧
  (FST (HD s.contexts)).jumpDest = NONE
  ⇒
  (FST (HD s'.contexts)).jumpDest = NONE
Proof
  cheat  (* SCAFFOLD *)
QED

(* handle_step preserves all_jumpDest_NONE *)
Theorem preserves_all_jumpDest_NONE_handle_step[simp]:
  preserves_all_jumpDest_NONE (handle_step e)
Proof
  cheat  (* SCAFFOLD *)
QED

(* For step_inst on non-call/create ops, we use the bridge lemma.
   They satisfy preserves_jumpDest and preserves_same_frame. *)

Theorem preserves_all_jumpDest_NONE_dispatch_precompiles[simp]:
  preserves_all_jumpDest_NONE (dispatch_precompiles a)
Proof
  cheat  (* SCAFFOLD *)
QED

(* step_call and step_create preserve all_jumpDest_NONE *)
(* Step helpers: use bridge lemma with preserves_jumpDest + preserves_same_frame *)

Theorem preserves_all_jumpDest_NONE_step_binop[simp]:
  preserves_all_jumpDest_NONE (step_binop op f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_monop[simp]:
  preserves_all_jumpDest_NONE (step_monop op f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_modop[simp]:
  preserves_all_jumpDest_NONE (step_modop op f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_context[simp]:
  preserves_all_jumpDest_NONE (step_context op f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_msgParams[simp]:
  preserves_all_jumpDest_NONE (step_msgParams op f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_txParams[simp]:
  preserves_all_jumpDest_NONE (step_txParams op f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_exp[simp]:
  preserves_all_jumpDest_NONE step_exp
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_keccak256[simp]:
  preserves_all_jumpDest_NONE step_keccak256
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_balance[simp]:
  preserves_all_jumpDest_NONE step_balance
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_call_data_load[simp]:
  preserves_all_jumpDest_NONE step_call_data_load
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_copy_to_memory[simp]:
  (∀f. getter = SOME f ⇒ preserves_jumpDest f) ∧
  (∀f. getter = SOME f ⇒ preserves_same_frame f)
  ⇒
  preserves_all_jumpDest_NONE (step_copy_to_memory op getter)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_return_data_copy[simp]:
  preserves_all_jumpDest_NONE step_return_data_copy
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_ext_code_size[simp]:
  preserves_all_jumpDest_NONE step_ext_code_size
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_ext_code_copy[simp]:
  preserves_all_jumpDest_NONE step_ext_code_copy
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_ext_code_hash[simp]:
  preserves_all_jumpDest_NONE step_ext_code_hash
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_block_hash[simp]:
  preserves_all_jumpDest_NONE step_block_hash
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_blob_hash[simp]:
  preserves_all_jumpDest_NONE step_blob_hash
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_self_balance[simp]:
  preserves_all_jumpDest_NONE step_self_balance
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_pop[simp]:
  preserves_all_jumpDest_NONE step_pop
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_mload[simp]:
  preserves_all_jumpDest_NONE step_mload
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_mstore[simp]:
  preserves_all_jumpDest_NONE (step_mstore op)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_sload[simp]:
  preserves_all_jumpDest_NONE (step_sload t)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_sstore[simp]:
  preserves_all_jumpDest_NONE (step_sstore t)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_push[simp]:
  preserves_all_jumpDest_NONE (step_push n l)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_dup[simp]:
  preserves_all_jumpDest_NONE (step_dup n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_swap[simp]:
  preserves_all_jumpDest_NONE (step_swap n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_dupn[simp]:
  preserves_all_jumpDest_NONE step_dupn
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_swapn[simp]:
  preserves_all_jumpDest_NONE step_swapn
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_exchange[simp]:
  preserves_all_jumpDest_NONE step_exchange
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_log[simp]:
  preserves_all_jumpDest_NONE (step_log n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_return[simp]:
  preserves_all_jumpDest_NONE (step_return b)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_self_destruct[simp]:
  preserves_all_jumpDest_NONE step_self_destruct
Proof
  cheat  (* SCAFFOLD *)
QED

(* Call/Create helpers *)

Theorem preserves_all_jumpDest_NONE_proceed_call[simp]:
  preserves_all_jumpDest_NONE (proceed_call a b c d e f g h s)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_call[simp]:
  preserves_all_jumpDest_NONE (step_call op)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_proceed_create:
  preserves_all_jumpDest_NONE (proceed_create a b c d e)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem preserves_all_jumpDest_NONE_step_create[simp]:
  preserves_all_jumpDest_NONE (step_create two)
Proof
  cheat  (* SCAFFOLD *)
QED

(* step_inst preserves all_jumpDest_NONE for all opcodes *)
Theorem preserves_all_jumpDest_NONE_step_inst[simp]:
  op ≠ Jump ∧ op ≠ JumpI ⇒
  preserves_all_jumpDest_NONE (step_inst op)
Proof
  cheat  (* SCAFFOLD *)
QED

(* The inner do-block of step: INL case preserves all_jumpDest_NONE *)
Theorem step_inner_INL_preserves_all_jumpDest_NONE:
  (do
    context <- get_current_context;
    case FLOOKUP context.msgParams.parsed context.pc of
    | SOME op => do step_inst op; inc_pc_or_jump op od
    | NONE =>
        if LENGTH context.msgParams.code ≤ context.pc then step_inst Stop
        else step_inst Invalid
  od) s = (INL x, s') ∧ all_jumpDest_NONE s ⇒ all_jumpDest_NONE s'
Proof
  cheat  (* SCAFFOLD *)
QED

(* ----------------------------------------------------------------- *)
(* Bridge: same_frame_rel implies TL preservation                    *)
(* ----------------------------------------------------------------- *)

Theorem same_frame_rel_TL:
  same_frame_rel s s' ⇒ TL s'.contexts = TL s.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

(*) handle_step INL establishes all_jumpDest_NONE given only TL has jumpDest NONE.

   Motivation: when the inner block of step returns INR because step_inst Jump
   set jumpDest = SOME pc and inc_pc_or_jump failed with InvalidJumpDest, the
   intermediate state s'' has a dirty head but a clean tail. handle_step then
   pops the dirty head (it can't reraise with n > 1 because popping returns INL),
   exposing position 1 as the new head, which has jumpDest = NONE. The
   post-pop operations (inc_pc, push_stack, set_return_data, etc.) don't
   touch jumpDest. So all_jumpDest_NONE holds on the final state.

   This is strictly weaker than preserves_all_jumpDest_NONE_handle_step,
   which requires all_jumpDest_NONE on the input. That stronger lemma can't
   handle the Jump/JumpI + InvalidJumpDest sub-case because the head is dirty.
   *)
Theorem handle_step_INL_ESTABLISHES_all_jumpDest_NONE:
  handle_step e s = (INL (), s') ∧ s.contexts ≠ [] ∧
  EVERY (λc. (FST c).jumpDest = NONE) (TL s.contexts) ⇒
  all_jumpDest_NONE s'
Proof
  cheat  (* SCAFFOLD *)
QED

(* Main theorem: step INL preserves all_jumpDest_NONE *)
Theorem step_all_jumpDest_NONE:
  step s = (INL (), s') ∧ all_jumpDest_NONE s ⇒ all_jumpDest_NONE s'
Proof
  cheat  (* SCAFFOLD *)
QED

(* Derived theorem: if all contexts have jumpDest = NONE and contexts ≠ [],
   then HD s'.contexts has jumpDest = NONE *)
Theorem step_jumpDest_NONE:
  step s = (INL (), s') ∧ all_jumpDest_NONE s ∧ s'.contexts ≠ []
  ⇒ (FST (HD s'.contexts)).jumpDest = NONE
Proof
  cheat  (* SCAFFOLD *)
QED
