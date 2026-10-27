(*
 * `run_within_frame` preservation theorems.
 *
 * Application layer that composes the four underlying frameworks
 * into the headline `run_within_frame_preserves` theorem and its
 * named downstream corollaries. The frameworks live in:
 *
 *   - `vfmSameFrame`: `same_frame_rel`, `preserves_same_frame`,
 *     `psf`, per-opcode / per-precompile [simp] lemmas,
 *     `outputTo_consistent`, SELFDESTRUCT psf details,
 *     `proceed_call_length`, `proceed_create_length`.
 *   - `vfmStepLength`: `same_frame_or_grow`, `psf_or_grow`,
 *     `length_preserves`, `length_or_inl_grow`, and associated
 *     step_call / step_create structural lemmas.
 *   - `vfmMsdomainPreserved`: `SND_*_msdomain[simp]` leaves and
 *     `SND_handle_step_msdomain`.
 *   - `vfmHandleStep`: `psf_handle_create`,
 *     `handle_exception_same_frame`, `handle_step_same_frame`,
 *     state-effect lemmas for set_rollback / pop_context /
 *     push_context, `pop_and_incorporate_context_failure_effect`,
 *     `handle_exception_pop_*` / `handle_step_pop_*` memory-effect
 *     lemmas.
 *
 * This theory adds:
 *   - `bind_inr_grow_factor` / `ignore_bind_inr_grow_factor`: peel
 *     a preserves_same_frame prefix off an INR-growing bind chain,
 *     locating the state just before the growth-causing step.
 *   - The `inr_grow_witness` framework and `inr_grow_P`:
 *     compositional predicate machinery characterising INR-grow
 *     outcomes.
 *   - `step_call_inr_grow_structure`: structural description of the
 *     state after step_call INR-grows.
 *   - `step_call_handle_step_inr_grow_same_frame`: push then pop
 *     composes to same-frame.
 *   - `step_same_frame`: step preserves same-frame on length-
 *     preserving transitions.
 *   - `run_within_frame_preserves`, `run_within_frame_gas_monotone`:
 *     the headline OWHILE-iterated theorems.
 *   - Named downstream corollaries `run_within_frame_preserves_*`
 *     exposing individual conjuncts of `same_frame_rel` for user
 *     consumption (txParams, storage / tStorage / code / nonce
 *     outside the callee, non-head contexts, saved_rollback,
 *     callee nonce monotone, logs grow, accesses grow, refund
 *     monotone, domain compatible).
 *)
Theory vfmRunWithinFrame
Ancestors
  arithmetic combin list pair pred_set finite_set rich_list
  vfmState vfmContext vfmExecution vfmExecutionProp
  vfmStaticCalls vfmTxParams vfmDomainSeparation vfmDecreasesGas
  vfmSameFrame vfmStepLength vfmMsdomainPreserved vfmHandleStep
Libs
  BasicProvers

val _ = Parse.hide "add"
val _ = Parse.hide "from"

(* Projection rules keep original-account reasoning independent of frames. *)
Theorem original_bind[local]:
  (!s. (SND (g s)).originalAccounts = s.originalAccounts) /\
  (!x s. (SND (f x s)).originalAccounts = s.originalAccounts) ==>
  !s. (SND (bind g f s)).originalAccounts = s.originalAccounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem original_ignore_bind[local]:
  (!s. (SND (g s)).originalAccounts = s.originalAccounts) /\
  (!s. (SND (f s)).originalAccounts = s.originalAccounts) ==>
  !s. (SND (ignore_bind g f s)).originalAccounts = s.originalAccounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem original_handle[local]:
  (!s. (SND (g s)).originalAccounts = s.originalAccounts) /\
  (!e s. (SND (f e s)).originalAccounts = s.originalAccounts) ==>
  !s. (SND (handle g f s)).originalAccounts = s.originalAccounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem original_cond[local]:
  (!s. (SND (m s)).originalAccounts = s.originalAccounts) /\
  (!s. (SND (n s)).originalAccounts = s.originalAccounts) ==>
  !s. (SND ((if b then m else n) s)).originalAccounts = s.originalAccounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem original_primitives[local]:
  (!x s. (SND (return x s)).originalAccounts = s.originalAccounts) /\
  (!e s. (SND (fail e s)).originalAccounts = s.originalAccounts) /\
  (!e s. (SND (reraise e s)).originalAccounts = s.originalAccounts) /\
  (!b e s. (SND (assert b e s)).originalAccounts = s.originalAccounts) /\
  (!s. (SND (get_current_context s)).originalAccounts = s.originalAccounts) /\
  (!c s. (SND (set_current_context c s)).originalAccounts = s.originalAccounts) /\
  (!s. (SND (get_num_contexts s)).originalAccounts = s.originalAccounts) /\
  (!cr s. (SND (push_context cr s)).originalAccounts = s.originalAccounts) /\
  (!s. (SND (pop_context s)).originalAccounts = s.originalAccounts) /\
  (!s. (SND (get_accounts s)).originalAccounts = s.originalAccounts) /\
  (!s. (SND (get_rollback s)).originalAccounts = s.originalAccounts) /\
  (!rb s. (SND (set_rollback rb s)).originalAccounts = s.originalAccounts) /\
  (!f s. (SND (update_accounts f s)).originalAccounts = s.originalAccounts) /\
  (!d s. (SND (set_domain d s)).originalAccounts = s.originalAccounts)
Proof
  cheat  (* SCAFFOLD *)
QED

val original_tac = rpt
  (FIRST [irule original_bind, irule original_ignore_bind,
          irule original_cond, irule original_handle]
   >> rpt conj_tac >> rpt gen_tac >> simp[original_primitives]);

Theorem original_context_wrappers[local]:
  (!s. (SND (get_gas_left s)).originalAccounts = s.originalAccounts) /\
  (!s. (SND (get_callee s)).originalAccounts = s.originalAccounts) /\
  (!s. (SND (get_caller s)).originalAccounts = s.originalAccounts) /\
  (!s. (SND (get_value s)).originalAccounts = s.originalAccounts) /\
  (!s. (SND (get_static s)).originalAccounts = s.originalAccounts) /\
  (!s. (SND (get_return_data s)).originalAccounts = s.originalAccounts) /\
  (!s. (SND (get_output_to s)).originalAccounts = s.originalAccounts) /\
  (!d s. (SND (set_return_data d s)).originalAccounts = s.originalAccounts) /\
  (!n s. (SND (consume_gas n s)).originalAccounts = s.originalAccounts) /\
  (!n s. (SND (unuse_gas n s)).originalAccounts = s.originalAccounts) /\
  (!n s. (SND (pop_stack n s)).originalAccounts = s.originalAccounts) /\
  (!v s. (SND (push_stack v s)).originalAccounts = s.originalAccounts) /\
  (!ls s. (SND (push_logs ls s)).originalAccounts = s.originalAccounts) /\
  (!ad sd s. (SND (update_gas_refund (ad,sd) s)).originalAccounts = s.originalAccounts) /\
  (!s. (SND (inc_pc s)).originalAccounts = s.originalAccounts) /\
  (!n s. (SND (expand_memory n s)).originalAccounts = s.originalAccounts) /\
  (!a n s. (SND (read_memory a n s)).originalAccounts = s.originalAccounts) /\
  (!a bs s. (SND (write_memory a bs s)).originalAccounts = s.originalAccounts) /\
  (!a n s. (SND (memory_expansion_info a n s)).originalAccounts = s.originalAccounts)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem original_pop_and_incorporate[local]:
  !s. (SND (pop_and_incorporate_context success s)).originalAccounts = s.originalAccounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem original_push_dispatch[local]:
  !s. (SND (ignore_bind (push_context cr) (dispatch_precompiles a) s)).originalAccounts = s.originalAccounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem original_access_address[local]:
  !s. (SND (access_address a s)).originalAccounts = s.originalAccounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem original_call_wrappers[local]:
  (!s. (SND (assert_not_static s)).originalAccounts = s.originalAccounts) /\
  (!n s. (SND (abort_unuse n s)).originalAccounts = s.originalAccounts) /\
  (!n s. (SND (abort_call_value n s)).originalAccounts = s.originalAccounts)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem original_handle_create[local]:
  !s. (SND (handle_create e s)).originalAccounts = s.originalAccounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem original_handle_exception[local]:
  !s. (SND (handle_exception e s)).originalAccounts = s.originalAccounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem handle_step_original_accounts[local]:
  handle_step e s = (r,t) ==> t.originalAccounts = s.originalAccounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem original_proceed_call[local]:
  !s. (SND (proceed_call op sender address value ao az code stipend ot s)).originalAccounts = s.originalAccounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem original_step_call[local]:
  !s. (SND (step_call op s)).originalAccounts = s.originalAccounts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_original_accounts[local]:
  step_call op s = (r,t) ==> t.originalAccounts = s.originalAccounts
Proof
  cheat  (* SCAFFOLD *)
QED



(* ================================================================ *)
(* Framework: INR-grow structure witness.                             *)
(*                                                                    *)
(* When a bind chain g;f INR-grows and g preserves_same_frame, the    *)
(* INR-grow must come from f (since preserves_same_frame implies     *)
(* length preservation). This lets us "peel off" prefix layers to    *)
(* locate the state just before the growth-causing step.             *)
(* ================================================================ *)

Theorem bind_inr_grow_factor:
  preserves_same_frame g ∧
  bind g f s = (INR e, s1) ∧
  s.contexts ≠ [] ∧
  LENGTH s1.contexts > LENGTH s.contexts ⇒
    ∃x sp. g s = (INL x, sp) ∧ same_frame_rel s sp ∧
            f x sp = (INR e, s1)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem ignore_bind_inr_grow_factor:
  preserves_same_frame g ∧
  ignore_bind g f s = (INR e, s1) ∧
  s.contexts ≠ [] ∧
  LENGTH s1.contexts > LENGTH s.contexts ⇒
    ∃sp. g s = (INL (), sp) ∧ same_frame_rel s sp ∧
         f sp = (INR e, s1)
Proof
  cheat  (* SCAFFOLD *)
QED

(* ---------------- inr_grow_witness predicate ------------------- *)

(* `inr_grow_witness P m` says: whenever m INR-grows from a state s,
   there exists a sp with same_frame_rel s sp such that P holds of
   (sp, s1, e).

   This is compositional: we can chain preserves_same_frame prefixes
   onto any inr_grow_witness f, giving inr_grow_witness (bind g f). *)
Definition inr_grow_witness_def:
  inr_grow_witness (P: execution_state -> execution_state -> exception option -> bool)
                   (m: unit execution) ⇔
    ∀s e s1. m s = (INR e, s1) ∧ s.contexts ≠ [] ∧
             LENGTH s1.contexts > LENGTH s.contexts ⇒
      ∃sp. same_frame_rel s sp ∧ P sp s1 e
End

(* Strengthen: if P sp s1 e implies Q sp s1 e, then witness with P
   gives witness with Q. *)
Theorem inr_grow_witness_mono:
  inr_grow_witness P m ∧ (∀sp s1 e. P sp s1 e ⇒ Q sp s1 e) ⇒
  inr_grow_witness Q m
Proof
  cheat  (* SCAFFOLD *)
QED

(* Composition: preserves_same_frame prefix + inr_grow_witness tail. *)
Theorem inr_grow_witness_bind_preserves_g:
  preserves_same_frame g ∧ (∀x. inr_grow_witness P (f x)) ⇒
  inr_grow_witness P (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_grow_witness_ignore_bind_preserves_g:
  preserves_same_frame g ∧ inr_grow_witness P f ⇒
  inr_grow_witness P (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_grow_witness_cond[simp]:
  inr_grow_witness P m1 ∧ inr_grow_witness P m2 ⇒
  inr_grow_witness P (if b then m1 else m2)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_grow_witness_case_option[simp]:
  inr_grow_witness P m_none ∧ (∀x. inr_grow_witness P (m_some x)) ⇒
  inr_grow_witness P (case opt of NONE => m_none | SOME x => m_some x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_grow_witness_let[simp]:
  (∀x. inr_grow_witness P (f x)) ⇒
  inr_grow_witness P (let x = v in f x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_grow_witness_case_pair[simp]:
  (∀a b. inr_grow_witness P (f a b)) ⇒
  inr_grow_witness P (case p of (a, b) => f a b)
Proof
  cheat  (* SCAFFOLD *)
QED

(* From preserves_same_frame: m never INR-grows, so witness is
   vacuously true. *)
Theorem inr_grow_witness_of_preserves_same_frame:
  preserves_same_frame m ⇒ inr_grow_witness P m
Proof
  cheat  (* SCAFFOLD *)
QED

(* Predicate capturing the INR-grow structure we want from
   step_call / proceed_call.

   `inr_grow_P outputTo sp s1 e` says that s1 results from proceed_call
   (after some prefix) with outputTo parameter, exhibiting:
   - e is not vfm_abort and not SOME Reverted
   - callee_local_changes, accesses grow, msdomain grow
   - s1.contexts structure has the pushed child + original parent + rest *)
Definition inr_grow_P_def:
  inr_grow_P sp s1 e ⇔
    ¬ vfm_abort e ∧ e ≠ SOME Reverted ∧
    callee_local_changes
      (FST (HD sp.contexts)).msgParams.callee sp.rollback s1.rollback ∧
    toSet sp.rollback.accesses.addresses ⊆
      toSet s1.rollback.accesses.addresses ∧
    toSet sp.rollback.accesses.storageKeys ⊆
      toSet s1.rollback.accesses.storageKeys ∧
    msdomain_compatible sp.msdomain s1.msdomain ∧
    (∃callee_ctx parent_ctx mr.
      s1.contexts = (callee_ctx, sp.rollback) ::
                    (parent_ctx, SND (HD sp.contexts)) ::
                    TL sp.contexts ∧
      parent_ctx.msgParams = (FST (HD sp.contexts)).msgParams ∧
      parent_ctx.logs = (FST (HD sp.contexts)).logs ∧
      parent_ctx.addRefund = (FST (HD sp.contexts)).addRefund ∧
      parent_ctx.subRefund = (FST (HD sp.contexts)).subRefund ∧
      callee_ctx.msgParams.outputTo = Memory mr)
End



(* The `push_context (ctx, rb) ; dispatch_precompiles a` pattern:
   push_context grows by 1 and returns INL. dispatch_precompiles is
   preserves_same_frame so it may INR but doesn't further grow.

   When this composed monad INR-grows, we extract structural info. *)

(* ---- Framework: `inr_ok_exn` ----------------------------------- *)

(* A monad `m` is `inr_ok_exn` when every INR result it returns from
   a non-empty-contexts state is neither a `vfm_abort` nor `SOME
   Reverted`. The `s.contexts ≠ []` hypothesis is needed because the
   context-dependent primitives `get_current_context` /
   `set_current_context` raise `Impossible` (a `vfm_abort`) when
   contexts are empty; under that hypothesis they don't.

   Usage mirrors `preserves_same_frame`: compositional rules applied
   explicitly (`irule`), leaf lemmas for the few primitives the
   precompile bodies actually call. *)
Definition inr_ok_exn_def:
  inr_ok_exn (m : α execution) ⇔
    ∀s r s'. m s = (r, s') ∧ s.contexts ≠ [] ⇒
      ∀e. r = INR e ⇒ ¬ vfm_abort e ∧ e ≠ SOME Reverted
End

(* ---- Composition lemmas --------------------------------------- *)

(* bind composition requires that the prefix `g` also preserves the
   non-emptiness of contexts (so that `f x` runs with a non-empty
   stack). For the precompile bodies, we only compose with
   `preserves_same_frame` primitives whose non-emptiness preservation
   follows from `same_frame_rel_contexts_ne`. *)
Theorem inr_ok_exn_bind:
  preserves_same_frame g ∧ inr_ok_exn g ∧ (∀x. inr_ok_exn (f x)) ⇒
  inr_ok_exn (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_ignore_bind:
  preserves_same_frame g ∧ inr_ok_exn g ∧ inr_ok_exn f ⇒
  inr_ok_exn (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_cond:
  inr_ok_exn m1 ∧ inr_ok_exn m2 ⇒
  inr_ok_exn (if b then m1 else m2)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_case_option:
  inr_ok_exn m_none ∧ (∀x. inr_ok_exn (m_some x)) ⇒
  inr_ok_exn (case opt of NONE => m_none | SOME x => m_some x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_case_pair:
  (∀x y. inr_ok_exn (f x y)) ⇒
  inr_ok_exn (case pr of (x, y) => f x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_let:
  (∀x. inr_ok_exn (f x)) ⇒ inr_ok_exn (let x = v in f x)
Proof
  cheat  (* SCAFFOLD *)
QED

(* ---- Leaf lemmas: primitives used inside precompile bodies ---- *)

Theorem inr_ok_exn_return[simp]:
  inr_ok_exn (return x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_fail_OutOfGas[simp]:
  inr_ok_exn (fail OutOfGas)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_fail_InvalidParameter[simp]:
  inr_ok_exn (fail InvalidParameter)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_fail_KZGProofError[simp]:
  inr_ok_exn (fail KZGProofError)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_assert_OutOfGas[simp]:
  inr_ok_exn (assert b OutOfGas)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_assert_KZGProofError[simp]:
  inr_ok_exn (assert b KZGProofError)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_finish[simp]:
  inr_ok_exn finish
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_get_call_data[simp]:
  inr_ok_exn get_call_data
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_consume_gas[simp]:
  inr_ok_exn (consume_gas n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_set_return_data[simp]:
  inr_ok_exn (set_return_data d)
Proof
  cheat  (* SCAFFOLD *)
QED

(* ---- Per-precompile `inr_ok_exn` lemmas ----------------------- *)

(* Each precompile body is built from `get_call_data`, `consume_gas`,
   `set_return_data`, `finish`, `fail {OOG,IP,KZG}`, `assert _ {OOG,KZG}`
   and `case ... of NONE / SOME / (a, b)` combinators. The structural
   proof pattern mirrors the `preserves_same_frame_precompile_*`
   lemmas: unfold the definition, then `irule` bind / ignore_bind /
   case_option / case_pair composition rules down to the leaves. *)

Theorem inr_ok_exn_precompile_ecrecover:
  inr_ok_exn precompile_ecrecover
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_precompile_sha2_256:
  inr_ok_exn precompile_sha2_256
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_precompile_ripemd_160:
  inr_ok_exn precompile_ripemd_160
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_precompile_identity:
  inr_ok_exn precompile_identity
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_precompile_modexp:
  inr_ok_exn precompile_modexp
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_precompile_ecadd:
  inr_ok_exn precompile_ecadd
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_precompile_ecmul:
  inr_ok_exn precompile_ecmul
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_precompile_ecpairing:
  inr_ok_exn precompile_ecpairing
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_precompile_blake2f:
  inr_ok_exn precompile_blake2f
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_precompile_point_eval:
  inr_ok_exn precompile_point_eval
Proof
  cheat  (* SCAFFOLD *)
QED

(* The BLS precompiles share a common shape:
     get_call_data ; consume_gas N ;
     case f input of NONE => fail OutOfGas
                   | SOME r => set_return_data r ; finish *)
Theorem inr_ok_exn_precompile_bls_g1add:
  inr_ok_exn precompile_bls_g1add
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_precompile_bls_g1msm:
  inr_ok_exn precompile_bls_g1msm
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_precompile_bls_g2add:
  inr_ok_exn precompile_bls_g2add
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_precompile_bls_g2msm:
  inr_ok_exn precompile_bls_g2msm
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_precompile_bls_pairing:
  inr_ok_exn precompile_bls_pairing
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_precompile_bls_map_fp_to_g1:
  inr_ok_exn precompile_bls_map_fp_to_g1
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_precompile_bls_map_fp2_to_g2:
  inr_ok_exn precompile_bls_map_fp2_to_g2
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem inr_ok_exn_precompile_p256verify:
  inr_ok_exn precompile_p256verify
Proof
  cheat  (* SCAFFOLD *)
QED

(* ---- Helper: precompile bodies only raise OOG/IP/KZG ---------- *)

(* When `a` is a precompile address (ruling out the `fail Impossible`
   default), any INR exception raised by dispatch_precompiles is
   neither `SOME Reverted` nor a `vfm_abort`. *)
Theorem dispatch_precompiles_inr_not_reverted_not_abort:
  s.contexts ≠ [] ∧
  fIN a precompile_addresses ∧
  dispatch_precompiles a s = (INR e, s') ⇒
    ¬ vfm_abort e ∧ e ≠ SOME Reverted
Proof
  cheat  (* SCAFFOLD *)
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
(* Lift `psf_update_accounts_transfer_value` (which uses `psf (λs.T)`)
   to a `preserves_same_frame` simp rule, so that the prefix-peeling
   tactic applies uniformly through the transfer_value step. *)
Theorem preserves_same_frame_update_accounts_transfer_value[local,simp]:
  preserves_same_frame
    (update_accounts (transfer_value fromAddr toAddr amount))
Proof
  cheat  (* SCAFFOLD *)
QED

(* Witness for proceed_call with outputTo = Memory mr: when it
   INR-grows, the inr_grow_P structure holds of the entering state sp
   and the final state s1. *)
Theorem inr_grow_witness_proceed_call:
  inr_grow_witness inr_grow_P
    (proceed_call op sender address value aOff aSz code stipend
                  (Memory mr))
Proof
  cheat  (* SCAFFOLD *)
QED

(* Main witness lemma: step_call's INR-growth carries the full
   inr_grow_P structure (not just the weaker same-frame-or-grow
   disjunction). *)
Theorem inr_grow_witness_step_call:
  inr_grow_witness inr_grow_P (step_call op)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_call_inr_grow_structure:
  s.contexts ≠ [] ∧ outputTo_consistent s ∧
  step_call op s = (INR e, s1) ∧
  LENGTH s1.contexts > LENGTH s.contexts ⇒
    ¬ vfm_abort e ∧ e ≠ SOME Reverted ∧
    (∃sp callee_ctx callee_rb mr.
       same_frame_rel s sp ∧
       callee_rb = sp.rollback ∧
       (* Relationship between s1.rollback and sp.rollback:
          - callee_local_changes (sp's callee) sp.rollback s1.rollback:
            transfer_value (if called) modifies only balance;
            precompile bodies don't touch rollback.
          - Accesses grow monotonically.
          - msdomain grows monotonically. *)
       callee_local_changes
         (FST (HD sp.contexts)).msgParams.callee
         sp.rollback s1.rollback ∧
       toSet sp.rollback.accesses.addresses ⊆
         toSet s1.rollback.accesses.addresses ∧
       toSet sp.rollback.accesses.storageKeys ⊆
         toSet s1.rollback.accesses.storageKeys ∧
       msdomain_compatible sp.msdomain s1.msdomain ∧
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
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

(* When the step inner computation INR-grows, the exception is not a
   vfm_abort. This follows because:
   - Stop/Invalid are preserves_same_frame, can't grow
   - For other ops that grew: by step_inst_inr_grew_is_call_family, op is Call-family
   - For Call-family ops: by step_call_inr_grow_structure, ¬vfm_abort e *)
Theorem step_inner_inr_grow_not_abort:
  s.contexts ≠ [] ∧ outputTo_consistent s ∧
  (do
     context <- get_current_context;
     case FLOOKUP context.msgParams.parsed context.pc of
     | SOME op => do step_inst op; inc_pc_or_jump op od
     | NONE =>
         if LENGTH context.msgParams.code ≤ context.pc then step_inst Stop
         else step_inst Invalid
   od) s = (INR e, s') ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  ¬vfm_abort e
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_same_frame:
  outputTo_consistent s ∧
  step s = (r, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  same_frame_rel s s'
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

(* ================================================================ *)
(* Gas monotonicity corollary (separate from same_frame_rel).        *)
(* ================================================================ *)

Theorem step_same_frame_gas_monotone:
  outputTo_consistent s ∧ s.contexts ≠ [] ∧
  EVERY (wf_context o FST) s.contexts ∧ step s = (r, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  (FST (HD s.contexts)).gasUsed ≤ (FST (HD s'.contexts)).gasUsed
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_within_frame_gas_monotone:
  outputTo_consistent es ∧ wf_state es ∧
  run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  (FST (HD es.contexts)).gasUsed ≤ (FST (HD es'.contexts)).gasUsed
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

Theorem run_within_frame_preserves_storage_outside_callee:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  ∀a. a ≠ (FST (HD es.contexts)).msgParams.callee ⇒
      (lookup_account a es'.rollback.accounts).storage =
      (lookup_account a es.rollback.accounts).storage
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_within_frame_preserves_tStorage_outside_callee:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  ∀a. a ≠ (FST (HD es.contexts)).msgParams.callee ⇒
      es'.rollback.tStorage a = es.rollback.tStorage a
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_within_frame_preserves_code_outside_callee:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  ∀a. a ≠ (FST (HD es.contexts)).msgParams.callee ⇒
      (lookup_account a es'.rollback.accounts).code =
      (lookup_account a es.rollback.accounts).code
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_within_frame_preserves_nonce_outside_callee:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  ∀a. a ≠ (FST (HD es.contexts)).msgParams.callee ⇒
      (lookup_account a es'.rollback.accounts).nonce =
      (lookup_account a es.rollback.accounts).nonce
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_within_frame_preserves_nonhead_contexts:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  TL es'.contexts = TL es.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_within_frame_preserves_head_msgParams:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  (FST (HD es'.contexts)).msgParams = (FST (HD es.contexts)).msgParams
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_within_frame_preserves_saved_rollback:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  SND (HD es'.contexts) = SND (HD es.contexts)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_within_frame_callee_nonce_monotone:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  (lookup_account (FST (HD es.contexts)).msgParams.callee
      es.rollback.accounts).nonce ≤
  (lookup_account (FST (HD es.contexts)).msgParams.callee
      es'.rollback.accounts).nonce
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_within_frame_logs_grow:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  IS_PREFIX (FST (HD es'.contexts)).logs (FST (HD es.contexts)).logs
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_within_frame_accesses_grow:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  toSet es.rollback.accesses.addresses ⊆
    toSet es'.rollback.accesses.addresses ∧
  toSet es.rollback.accesses.storageKeys ⊆
    toSet es'.rollback.accesses.storageKeys
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_within_frame_refund_monotone:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  (FST (HD es.contexts)).addRefund ≤ (FST (HD es'.contexts)).addRefund ∧
  (FST (HD es.contexts)).subRefund ≤ (FST (HD es'.contexts)).subRefund
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem run_within_frame_domain_compatible:
  outputTo_consistent es ∧ run_within_frame es = SOME (r, es') ∧
  LENGTH es'.contexts = LENGTH es.contexts ⇒
  msdomain_compatible es.msdomain es'.msdomain
Proof
  cheat  (* SCAFFOLD *)
QED
