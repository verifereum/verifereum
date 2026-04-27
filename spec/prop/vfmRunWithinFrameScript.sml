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
  strip_tac
  >> fs[preserves_same_frame_def]
  >> `∀rr ss. g s = (rr, ss) ⇒ same_frame_rel s ss`
      by (rpt strip_tac
          >> first_x_assum drule >> simp[])
  >> Cases_on `g s`
  >> rename1 `g s = (q, sp)`
  >> Cases_on `q`
  >- (  (* g returned INL x *)
       qexists_tac `x` >> qexists_tac `sp`
       >> `same_frame_rel s sp` by (first_x_assum irule >> simp[])
       >> simp[]
       >> qpat_x_assum `bind _ _ _ = _` mp_tac
       >> simp[bind_def])
  (* g returned INR: sp ≠ s1 because same_frame_rel s sp gives equal
     lengths, but LENGTH s1 > LENGTH s. *)
  >> `same_frame_rel s sp` by (first_x_assum irule >> simp[])
  >> qpat_x_assum `monad_bind _ _ _ = _` mp_tac
  >> simp[bind_def]
  >> strip_tac
  >> spose_not_then strip_assume_tac
  >> fs[same_frame_rel_def]
QED

Theorem ignore_bind_inr_grow_factor:
  preserves_same_frame g ∧
  ignore_bind g f s = (INR e, s1) ∧
  s.contexts ≠ [] ∧
  LENGTH s1.contexts > LENGTH s.contexts ⇒
    ∃sp. g s = (INL (), sp) ∧ same_frame_rel s sp ∧
         f sp = (INR e, s1)
Proof
  rw[ignore_bind_def]
  >> drule_all bind_inr_grow_factor
  >> rw[]
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
  rw[inr_grow_witness_def] >> metis_tac[]
QED

(* Composition: preserves_same_frame prefix + inr_grow_witness tail. *)
Theorem inr_grow_witness_bind_preserves_g:
  preserves_same_frame g ∧ (∀x. inr_grow_witness P (f x)) ⇒
  inr_grow_witness P (bind g f)
Proof
  rw[inr_grow_witness_def]
  >> drule_all bind_inr_grow_factor
  >> strip_tac
  >> first_x_assum (qspec_then `x` mp_tac)
  >> rewrite_tac[inr_grow_witness_def]
  >> disch_then drule
  >> `sp.contexts ≠ []` by metis_tac[same_frame_rel_contexts_ne]
  >> `LENGTH s1.contexts > LENGTH sp.contexts`
       by (`LENGTH sp.contexts = LENGTH s.contexts` by fs[same_frame_rel_def]
           >> simp[])
  >> simp[]
  >> strip_tac
  >> qexists_tac `sp'`
  >> simp[]
  >> metis_tac[same_frame_rel_trans]
QED

Theorem inr_grow_witness_ignore_bind_preserves_g:
  preserves_same_frame g ∧ inr_grow_witness P f ⇒
  inr_grow_witness P (ignore_bind g f)
Proof
  rw[ignore_bind_def]
  >> irule inr_grow_witness_bind_preserves_g
  >> simp[]
QED

Theorem inr_grow_witness_cond[simp]:
  inr_grow_witness P m1 ∧ inr_grow_witness P m2 ⇒
  inr_grow_witness P (if b then m1 else m2)
Proof
  rw[]
QED

Theorem inr_grow_witness_case_option[simp]:
  inr_grow_witness P m_none ∧ (∀x. inr_grow_witness P (m_some x)) ⇒
  inr_grow_witness P (case opt of NONE => m_none | SOME x => m_some x)
Proof
  Cases_on `opt` >> rw[]
QED

Theorem inr_grow_witness_let[simp]:
  (∀x. inr_grow_witness P (f x)) ⇒
  inr_grow_witness P (let x = v in f x)
Proof
  rw[]
QED

Theorem inr_grow_witness_case_pair[simp]:
  (∀a b. inr_grow_witness P (f a b)) ⇒
  inr_grow_witness P (case p of (a, b) => f a b)
Proof
  Cases_on `p` >> rw[]
QED

(* From preserves_same_frame: m never INR-grows, so witness is
   vacuously true. *)
Theorem inr_grow_witness_of_preserves_same_frame:
  preserves_same_frame m ⇒ inr_grow_witness P m
Proof
  rw[preserves_same_frame_def, inr_grow_witness_def]
  >> first_x_assum drule_all
  >> rw[same_frame_rel_def]
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
  simp[inr_ok_exn_def, bind_def]
  >> strip_tac
  >> rpt gen_tac
  >> Cases_on `g s` >> rename1 `g s = (q, sm)`
  >> Cases_on `q` >> simp[]
  >- (
    (* g returned INL x. Use preserves_same_frame to get
       sm.contexts ≠ [], then apply (f x)'s inr_ok_exn. *)
    strip_tac
    >> `same_frame_rel s sm` by (
      qpat_x_assum `preserves_same_frame _` mp_tac
      >> rewrite_tac[preserves_same_frame_def]
      >> disch_then drule >> simp[])
    >> `sm.contexts ≠ []` by metis_tac[same_frame_rel_contexts_ne]
    >> metis_tac[])
  (* g returned INR y. r = INR y and s' = sm. Apply inr_ok_exn g. *)
  >> rw[]
  >> metis_tac[]
QED

Theorem inr_ok_exn_ignore_bind:
  preserves_same_frame g ∧ inr_ok_exn g ∧ inr_ok_exn f ⇒
  inr_ok_exn (ignore_bind g f)
Proof
  rw[ignore_bind_def] >> irule inr_ok_exn_bind >> simp[]
QED

Theorem inr_ok_exn_cond:
  inr_ok_exn m1 ∧ inr_ok_exn m2 ⇒
  inr_ok_exn (if b then m1 else m2)
Proof
  rw[]
QED

Theorem inr_ok_exn_case_option:
  inr_ok_exn m_none ∧ (∀x. inr_ok_exn (m_some x)) ⇒
  inr_ok_exn (case opt of NONE => m_none | SOME x => m_some x)
Proof
  Cases_on `opt` >> rw[]
QED

Theorem inr_ok_exn_case_pair:
  (∀x y. inr_ok_exn (f x y)) ⇒
  inr_ok_exn (case pr of (x, y) => f x y)
Proof
  Cases_on `pr` >> rw[]
QED

Theorem inr_ok_exn_let:
  (∀x. inr_ok_exn (f x)) ⇒ inr_ok_exn (let x = v in f x)
Proof
  rw[]
QED

(* ---- Leaf lemmas: primitives used inside precompile bodies ---- *)

Theorem inr_ok_exn_return[simp]:
  inr_ok_exn (return x)
Proof
  rw[inr_ok_exn_def, return_def]
QED

Theorem inr_ok_exn_fail_OutOfGas[simp]:
  inr_ok_exn (fail OutOfGas)
Proof
  rw[inr_ok_exn_def, fail_def]
QED

Theorem inr_ok_exn_fail_InvalidParameter[simp]:
  inr_ok_exn (fail InvalidParameter)
Proof
  rw[inr_ok_exn_def, fail_def]
QED

Theorem inr_ok_exn_fail_KZGProofError[simp]:
  inr_ok_exn (fail KZGProofError)
Proof
  rw[inr_ok_exn_def, fail_def]
QED

Theorem inr_ok_exn_assert_OutOfGas[simp]:
  inr_ok_exn (assert b OutOfGas)
Proof
  rw[inr_ok_exn_def, assert_def]
QED

Theorem inr_ok_exn_assert_KZGProofError[simp]:
  inr_ok_exn (assert b KZGProofError)
Proof
  rw[inr_ok_exn_def, assert_def]
QED

Theorem inr_ok_exn_finish[simp]:
  inr_ok_exn finish
Proof
  rw[inr_ok_exn_def, finish_def]
QED

Theorem inr_ok_exn_get_call_data[simp]:
  inr_ok_exn get_call_data
Proof
  rw[inr_ok_exn_def, get_call_data_def, bind_def,
     get_current_context_def, return_def, fail_def, AllCaseEqs()]
QED

Theorem inr_ok_exn_consume_gas[simp]:
  inr_ok_exn (consume_gas n)
Proof
  rw[inr_ok_exn_def, consume_gas_def, bind_def, ignore_bind_def,
     get_current_context_def, set_current_context_def,
     assert_def, return_def, fail_def, AllCaseEqs()]
  >> gvs[]
QED

Theorem inr_ok_exn_set_return_data[simp]:
  inr_ok_exn (set_return_data d)
Proof
  rw[inr_ok_exn_def, set_return_data_def, bind_def,
     get_current_context_def, set_current_context_def,
     return_def, fail_def, AllCaseEqs()]
  >> gvs[]
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
  rw[precompile_ecrecover_def]
  >> rpt (irule inr_ok_exn_bind >> simp[] >> gen_tac)
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
  >> BasicProvers.PURE_CASE_TAC >> simp[]
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
QED

Theorem inr_ok_exn_precompile_sha2_256:
  inr_ok_exn precompile_sha2_256
Proof
  rw[precompile_sha2_256_def]
  >> rpt (irule inr_ok_exn_bind >> simp[] >> gen_tac)
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
QED

Theorem inr_ok_exn_precompile_ripemd_160:
  inr_ok_exn precompile_ripemd_160
Proof
  rw[precompile_ripemd_160_def]
  >> rpt (irule inr_ok_exn_bind >> simp[] >> gen_tac)
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
  >> BasicProvers.PURE_CASE_TAC >> simp[]
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
QED

Theorem inr_ok_exn_precompile_identity:
  inr_ok_exn precompile_identity
Proof
  rw[precompile_identity_def]
  >> rpt (irule inr_ok_exn_bind >> simp[] >> gen_tac)
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
QED

Theorem inr_ok_exn_precompile_modexp:
  inr_ok_exn precompile_modexp
Proof
  rw[precompile_modexp_def, LET_THM]
  >> rpt (irule inr_ok_exn_bind >> simp[] >> gen_tac)
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
QED

Theorem inr_ok_exn_precompile_ecadd:
  inr_ok_exn precompile_ecadd
Proof
  rw[precompile_ecadd_def]
  >> rpt (irule inr_ok_exn_bind >> simp[] >> gen_tac)
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
  >> BasicProvers.PURE_CASE_TAC >> simp[]
  >> BasicProvers.PURE_CASE_TAC >> simp[]
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
QED

Theorem inr_ok_exn_precompile_ecmul:
  inr_ok_exn precompile_ecmul
Proof
  rw[precompile_ecmul_def]
  >> rpt (irule inr_ok_exn_bind >> simp[] >> gen_tac)
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
  >> BasicProvers.PURE_CASE_TAC >> simp[]
  >> BasicProvers.PURE_CASE_TAC >> simp[]
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
QED

Theorem inr_ok_exn_precompile_ecpairing:
  inr_ok_exn precompile_ecpairing
Proof
  rw[precompile_ecpairing_def]
  >> rpt (irule inr_ok_exn_bind >> simp[] >> gen_tac)
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
  >> irule inr_ok_exn_cond >> simp[]
  >> BasicProvers.PURE_CASE_TAC >> simp[]
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
QED

Theorem inr_ok_exn_precompile_blake2f:
  inr_ok_exn precompile_blake2f
Proof
  rw[precompile_blake2f_def]
  >> irule inr_ok_exn_bind >> simp[] >> gen_tac
  >> BasicProvers.PURE_CASE_TAC >> simp[]
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
  >> BasicProvers.PURE_CASE_TAC >> simp[]
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
QED

Theorem inr_ok_exn_precompile_point_eval:
  inr_ok_exn precompile_point_eval
Proof
  rw[precompile_point_eval_def]
  >> irule inr_ok_exn_bind >> simp[] >> gen_tac
  >> BasicProvers.PURE_CASE_TAC >> simp[]
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
  >> BasicProvers.PURE_CASE_TAC >> simp[]
  >> BasicProvers.PURE_CASE_TAC >> simp[]
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
QED

(* The BLS precompiles share a common shape:
     get_call_data ; consume_gas N ;
     case f input of NONE => fail OutOfGas
                   | SOME r => set_return_data r ; finish *)
Theorem inr_ok_exn_precompile_bls_g1add:
  inr_ok_exn precompile_bls_g1add
Proof
  rw[precompile_bls_g1add_def]
  >> rpt (irule inr_ok_exn_bind >> simp[] >> gen_tac)
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
  >> BasicProvers.PURE_CASE_TAC >> simp[]
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
QED

Theorem inr_ok_exn_precompile_bls_g1msm:
  inr_ok_exn precompile_bls_g1msm
Proof
  rw[precompile_bls_g1msm_def]
  >> rpt (irule inr_ok_exn_bind >> simp[] >> gen_tac)
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
  >> BasicProvers.PURE_CASE_TAC >> simp[]
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
QED

Theorem inr_ok_exn_precompile_bls_g2add:
  inr_ok_exn precompile_bls_g2add
Proof
  rw[precompile_bls_g2add_def]
  >> rpt (irule inr_ok_exn_bind >> simp[] >> gen_tac)
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
  >> BasicProvers.PURE_CASE_TAC >> simp[]
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
QED

Theorem inr_ok_exn_precompile_bls_g2msm:
  inr_ok_exn precompile_bls_g2msm
Proof
  rw[precompile_bls_g2msm_def]
  >> rpt (irule inr_ok_exn_bind >> simp[] >> gen_tac)
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
  >> BasicProvers.PURE_CASE_TAC >> simp[]
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
QED

Theorem inr_ok_exn_precompile_bls_pairing:
  inr_ok_exn precompile_bls_pairing
Proof
  rw[precompile_bls_pairing_def]
  >> rpt (irule inr_ok_exn_bind >> simp[] >> gen_tac)
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
  >> BasicProvers.PURE_CASE_TAC >> simp[]
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
QED

Theorem inr_ok_exn_precompile_bls_map_fp_to_g1:
  inr_ok_exn precompile_bls_map_fp_to_g1
Proof
  rw[precompile_bls_map_fp_to_g1_def]
  >> rpt (irule inr_ok_exn_bind >> simp[] >> gen_tac)
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
  >> BasicProvers.PURE_CASE_TAC >> simp[]
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
QED

Theorem inr_ok_exn_precompile_bls_map_fp2_to_g2:
  inr_ok_exn precompile_bls_map_fp2_to_g2
Proof
  rw[precompile_bls_map_fp2_to_g2_def]
  >> rpt (irule inr_ok_exn_bind >> simp[] >> gen_tac)
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
  >> BasicProvers.PURE_CASE_TAC >> simp[]
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
QED

Theorem inr_ok_exn_precompile_p256verify:
  inr_ok_exn precompile_p256verify
Proof
  rw[precompile_p256verify_def]
  >> rpt (irule inr_ok_exn_bind >> simp[] >> gen_tac)
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
  >> BasicProvers.PURE_CASE_TAC >> simp[]
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
  >> BasicProvers.PURE_CASE_TAC >> simp[]
  >> rpt (irule inr_ok_exn_ignore_bind >> simp[])
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
  rw[dispatch_precompiles_def]
  >> TRY (
    (* The 18 precompile branches: match via the `inr_ok_exn`
       property of each. *)
    qmatch_asmsub_abbrev_tac `pc s = (INR e, s')`
    >> `inr_ok_exn pc`
         by simp[Abbr`pc`, inr_ok_exn_precompile_ecrecover,
                 inr_ok_exn_precompile_sha2_256,
                 inr_ok_exn_precompile_ripemd_160,
                 inr_ok_exn_precompile_identity,
                 inr_ok_exn_precompile_modexp,
                 inr_ok_exn_precompile_ecadd,
                 inr_ok_exn_precompile_ecmul,
                 inr_ok_exn_precompile_ecpairing,
                 inr_ok_exn_precompile_blake2f,
                 inr_ok_exn_precompile_point_eval,
                 inr_ok_exn_precompile_bls_g1add,
                 inr_ok_exn_precompile_bls_g1msm,
                 inr_ok_exn_precompile_bls_g2add,
                 inr_ok_exn_precompile_bls_g2msm,
                 inr_ok_exn_precompile_bls_pairing,
                 inr_ok_exn_precompile_bls_map_fp_to_g1,
                 inr_ok_exn_precompile_bls_map_fp2_to_g2,
                 inr_ok_exn_precompile_p256verify]
    >> pop_assum mp_tac >> rewrite_tac[inr_ok_exn_def]
    >> disch_then drule
    >> simp[] >> NO_TAC)
  (* Default branch: `dispatch_precompiles a = fail Impossible`.
     Rule out via `fIN a precompile_addresses`. *)
  >> gvs[precompile_addresses_def, fIN_fset_ABS]
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
  rewrite_tac[preserves_same_frame_eq_psf_T]
  >> irule psf_update_accounts_transfer_value
QED

(* Witness for proceed_call with outputTo = Memory mr: when it
   INR-grows, the inr_grow_P structure holds of the entering state sp
   and the final state s1. *)
Theorem inr_grow_witness_proceed_call:
  inr_grow_witness inr_grow_P
    (proceed_call op sender address value aOff aSz code stipend
                  (Memory mr))
Proof
  (* Unfold proceed_call and analyse directly. Don't use
     `inr_grow_witness_bind_preserves_g` because it erases the
     `x = s.rollback` equation we need for the pushed rollback. *)
  simp[inr_grow_witness_def]
  >> rpt gen_tac >> strip_tac
  (* Witness: sp = s (the state entering proceed_call). The pushed
     rollback captured by get_rollback IS s.rollback. *)
  >> qexists_tac `s` >> simp[same_frame_rel_refl]
  (* Split on the transfer_value and precompile conditions first,
     then unfold proceed_call's body for each branch. *)
  >> Cases_on `s.contexts` >> gvs[]
  >> qpat_x_assum `proceed_call _ _ _ _ _ _ _ _ _ _ = _` mp_tac
  >> simp[proceed_call_def, bind_def, ignore_bind_def,
          get_rollback_def, read_memory_def, get_caller_def,
          get_value_def, get_static_def, update_accounts_def,
          push_context_def, get_current_context_def, return_def]
  >> `∀f. update_accounts f s = (INL (), s with rollback updated_by (λr. r with accounts updated_by f))`
       by simp[update_accounts_def, return_def]
  >> Cases_on `op ≠ CallCode ∧ 0 < value`
  >> Cases_on `fIN address precompile_addresses`
  >> gvs[return_def]
  >> strip_tac
  (* In the precompile branches, extract the exception-shape fact. *)
  >> drule_at (Pat`dispatch_precompiles`)
       dispatch_precompiles_inr_not_reverted_not_abort
  >> simp[]
  >> strip_tac
  >> simp[inr_grow_P_def]
  (* Extract cp facts and same_frame_rel facts about the
     dispatch_precompiles step. *)
  >> qmatch_asmsub_abbrev_tac `dispatch_precompiles address pushed`
  >> `pushed.contexts ≠ []` by (gvs[Abbr`pushed`])
  (* Extract cp facts: accounts/tStorage/toDelete preserved,
     contexts structure. *)
  >> drule (REWRITE_RULE [cp_def] (Q.SPEC `address` (GEN_ALL cp_dispatch_precompiles)))
  >> simp[]
  >> strip_tac
  >> drule (REWRITE_RULE [preserves_same_frame_def]
              (Q.SPEC `address` (GEN_ALL preserves_same_frame_dispatch_precompiles)))
  >> simp[]
  >> strip_tac
  (* Facts about `pushed`. *)
  >> `SND (HD pushed.contexts) = s.rollback ∧
      TL pushed.contexts = s.contexts ∧
      (FST (HD pushed.contexts)).msgParams.outputTo = Memory mr ∧
      pushed.rollback.accesses = s.rollback.accesses ∧
      pushed.msdomain = s.msdomain ∧
      (∀a. (lookup_account a pushed.rollback.accounts).storage =
           (lookup_account a s.rollback.accounts).storage) ∧
      (∀a. (lookup_account a pushed.rollback.accounts).code =
           (lookup_account a s.rollback.accounts).code) ∧
      (∀a. (lookup_account a pushed.rollback.accounts).nonce =
           (lookup_account a s.rollback.accounts).nonce) ∧
      pushed.rollback.tStorage = s.rollback.tStorage`
     by (gvs[Abbr`pushed`, initial_context_def, initial_msg_params_def,
             transfer_value_preserves_storage,
             transfer_value_preserves_code,
             transfer_value_preserves_nonce])
  >> gvs[]
  (* Extract same_frame_rel pushed s1 into its conjuncts. *)
  >> qpat_x_assum `same_frame_rel pushed s1` mp_tac
  >> rewrite_tac[same_frame_rel_def]
  >> strip_tac
  (* Pick parent_ctx = FST h for the existential. *)
  >> `∃parent_ctx.
       h = (parent_ctx, SND h) ∧ parent_ctx.msgParams = (FST h).msgParams ∧
       parent_ctx.logs = (FST h).logs ∧
       parent_ctx.addRefund = (FST h).addRefund ∧
       parent_ctx.subRefund = (FST h).subRefund`
     by (qexists_tac `FST h` >> simp[pairTheory.PAIR])
  (* Remaining: callee_local_changes, accesses ⊆, msdomain_compatible. *)
  >> simp[]
  >> fs[]
  >> simp[callee_local_changes_def]
  >> fs[callee_local_changes_def]
  >> metis_tac[]
QED

(* Main witness lemma: step_call's INR-growth carries the full
   inr_grow_P structure (not just the weaker same-frame-or-grow
   disjunction). *)
Theorem inr_grow_witness_step_call:
  inr_grow_witness inr_grow_P (step_call op)
Proof
  simp[step_call_def]
  >> irule inr_grow_witness_bind_preserves_g >> simp[] >> gen_tac
  >> pairarg_tac >> simp[]
  >> irule inr_grow_witness_bind_preserves_g >> simp[] >> gen_tac
  >> irule inr_grow_witness_bind_preserves_g >> simp[] >> gen_tac
  >> irule inr_grow_witness_bind_preserves_g >> simp[] >> gen_tac
  >> irule inr_grow_witness_bind_preserves_g >> simp[] >> gen_tac
  >> pairarg_tac >> simp[]
  >> irule inr_grow_witness_bind_preserves_g >> simp[] >> gen_tac
  >> pairarg_tac >> simp[]
  >> irule inr_grow_witness_ignore_bind_preserves_g >> simp[]
  >> irule inr_grow_witness_ignore_bind_preserves_g >> simp[]
  >> irule inr_grow_witness_ignore_bind_preserves_g >> simp[]
  >> irule inr_grow_witness_bind_preserves_g >> simp[] >> gen_tac
  >> irule inr_grow_witness_cond >> conj_tac
  >- (
    (* abort_call_value is preserves_same_frame, never INR-grows *)
    irule inr_grow_witness_of_preserves_same_frame >> simp[])
  >> irule inr_grow_witness_ignore_bind_preserves_g >> simp[]
  >> irule inr_grow_witness_bind_preserves_g >> simp[] >> gen_tac
  >> irule inr_grow_witness_cond >> conj_tac
  >- (
    (* abort_unuse is preserves_same_frame, never INR-grows *)
    irule inr_grow_witness_of_preserves_same_frame >> simp[])
  >> irule inr_grow_witness_proceed_call
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
  strip_tac
  >> mp_tac inr_grow_witness_step_call
  >> rewrite_tac[inr_grow_witness_def]
  >> disch_then drule
  >> simp[]
  >> strip_tac
  >> gvs[inr_grow_P_def]
  >> rpt (goal_assum (first_assum o mp_then Any mp_tac))
  >> simp[]
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
  (* Common txParams and msdomain reasoning for both branches. *)
  >> `s'.txParams = s.txParams` by (
       `s'.txParams = s1.txParams`
         by metis_tac[vfmTxParamsTheory.handle_step_preserves_txParams, SND]
       >> `s1.txParams = s.txParams`
         by metis_tac[vfmTxParamsTheory.step_call_preserves_txParams, SND]
       >> simp[])
  >> `s'.msdomain = s1.msdomain`
       by metis_tac[SND_handle_step_msdomain, SND]
  >> `msdomain_compatible sp.msdomain s'.msdomain` by simp[]
  >> `s.txParams = sp.txParams` by fs[same_frame_rel_def]
  >> Cases_on `e = NONE`
  >- (  (* Success case: e = NONE. Use _gen variant which handles
           q = INR post-pop finalization failures too. *)
       gvs[]
       >> drule handle_step_pop_success_memory_effect_gen
       >> disch_then (qspecl_then [`s'`, `q`] mp_tac)
       >> impl_tac >- simp[]
       >> strip_tac
       >> `s'.rollback = s1.rollback` by simp[]
       (* Prove same_frame_rel sp s': uses callee_local_changes
          from the structure lemma (sp → s1), plus the pop's
          structural effect. *)
       >> `same_frame_rel sp s'` by (
            simp[same_frame_rel_def]
            >> rpt conj_tac
            >> TRY (fs[] >> NO_TAC)
            >> fs[]
            >> TRY (fs[rich_listTheory.IS_PREFIX_APPEND] >> NO_TAC)
            >> decide_tac)
       >> metis_tac[same_frame_rel_trans])
  (* Failure case: e ≠ NONE. Use _gen variant. Need e ≠ SOME Reverted,
     which comes from the structure lemma (precompiles don't raise
     Reverted). *)
  >> drule handle_step_pop_memory_effect_gen
  >> disch_then (qspecl_then [`s'`, `q`, `e`] mp_tac)
  >> impl_tac >- simp[]
  >> strip_tac
  >> `s'.rollback = sp.rollback` by simp[]
  >> `same_frame_rel sp s'` by (
       simp[same_frame_rel_def, callee_local_changes_refl]
       >> fs[]
       >> rw[]
       >> fs[rich_listTheory.IS_PREFIX_APPEND]
       >> decide_tac)
  >> metis_tac[same_frame_rel_trans]
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
     if LENGTH context.msgParams.code ≤ context.pc then step_inst Stop
     else case FLOOKUP context.msgParams.parsed context.pc of
            NONE => step_inst Invalid
          | SOME op => do step_inst op; inc_pc_or_jump op od
   od) s = (INR e, s') ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  ¬vfm_abort e
Proof
  strip_tac
  >> gvs[bind_def, get_current_context_def, return_def, fail_def,
         COND_RATOR, vfmTypesTheory.option_CASE_rator, AllCaseEqs(),
         ignore_bind_def]
  (* Stop case: preserves_same_frame, can't grow - contradiction *)
  >- (`preserves_same_frame (step_inst Stop)` by simp[]
      >> imp_res_tac psf_imp_length_contexts_preserved
      >> gvs[])
  (* Invalid case: preserves_same_frame, can't grow - contradiction *)
  >- (`preserves_same_frame (step_inst Invalid)` by simp[]
      >> imp_res_tac psf_imp_length_contexts_preserved
      >> gvs[])
  (* SOME op case: step_inst op >>= inc_pc_or_jump op *)
  (* step_inst INL, inc_pc_or_jump INR: inc_pc_or_jump is psf, contradiction *)
  >- (`preserves_same_frame (inc_pc_or_jump op)` by simp[]
      >> drule_then drule psf_imp_length_contexts_preserved
        >> impl_tac
        >- (
          strip_tac >> gvs[inc_pc_or_jump_def, COND_RATOR, AllCaseEqs(), return_def]
          >> gvs[bind_def, AllCaseEqs(), get_current_context_def, fail_def] )
      >> strip_tac >> drule step_inst_inl_grew_is_call >> gvs[]
      >> strip_tac >> gvs[inc_pc_or_jump_def, return_def])
  (* step_inst INR with growth *)
  >> rename1 `step_inst op s = (INR e, s')`
  (* By step_inst_inr_grew_is_call_family, op is Call-family *)
  >> drule step_inst_inr_grew_is_call_family
  >> impl_tac >- gvs[]
  >> reverse(Cases_on`step_inst op s = step_call op s`)
  >- ( strip_tac >> gvs[step_inst_def] )
  (* By step_call_inr_grow_structure, ¬vfm_abort e *)
  >> gvs[]
  >> drule_all step_call_inr_grow_structure
  >> simp[]
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
