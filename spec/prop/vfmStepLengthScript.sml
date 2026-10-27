(*
 * Frameworks for reasoning about how monadic execution changes the
 * length of the context stack.
 *
 * The push / pop boundaries of a call frame violate
 * `preserves_same_frame` (they grow or shrink the stack). This theory
 * introduces two complementary frameworks — `same_frame_or_grow` /
 * `psf_or_grow` and `length_preserves` / `length_or_inl_grow` — that
 * track stack-length behaviour compositionally, and culminates in
 * structural lemmas about step_call / step_create:
 *
 *   - `same_frame_or_grow_step_call[simp]`,
 *     `same_frame_or_grow_step_create[simp]`,
 *     `step_call_same_frame`, `step_create_same_frame`;
 *   - `same_frame_or_grow_step_inst[simp]`,
 *     `same_frame_or_grow_step_inner[simp]`,
 *     `step_inst_inl_grew_is_call`;
 *   - `proceed_create_returns_inl`, `abort_unuse_length`,
 *     `abort_create_exists_length`;
 *   - the CREATE-family length framework: `length_or_inl_grow_*`
 *     primitives and composition lemmas;
 *   - `step_create_grown_returns_inl`, `step_create_inr_no_grow`,
 *     `step_inst_inr_grew_is_call_family`.
 *
 * Downstream theories use these to rule out the push / pop branches
 * via a length hypothesis when working inside a fixed frame.
 *)
Theory vfmStepLength
Ancestors
  arithmetic combin list pair pred_set finite_set rich_list
  vfmState vfmContext vfmExecution vfmExecutionProp
  vfmStaticCalls vfmTxParams vfmDomainSeparation vfmDecreasesGas
  vfmSameFrame
Libs
  BasicProvers

val _ = Parse.hide "add"
val _ = Parse.hide "from"

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

Theorem same_frame_or_grow_length:
  ∀m s r s'. same_frame_or_grow m ∧ m s = (r,s') ∧ s.contexts ≠ [] ⇒
    LENGTH s'.contexts ≥ LENGTH s.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem same_frame_or_grow_eq_length:
  ∀m s r s'. same_frame_or_grow m ∧ m s = (r,s') ∧ s.contexts ≠ [] ∧
    LENGTH s'.contexts = LENGTH s.contexts ⇒ same_frame_rel s s'
Proof
  cheat  (* SCAFFOLD *)
QED

(* ---------------- Bridge from preserves_same_frame -------------- *)

Theorem same_frame_or_grow_of_preserves[simp]:
  preserves_same_frame m ⇒ same_frame_or_grow m
Proof
  cheat  (* SCAFFOLD *)
QED

(* ---------------- Composition rules ----------------------------- *)

Theorem same_frame_or_grow_bind[simp]:
  same_frame_or_grow g ∧ (∀x. same_frame_or_grow (f x)) ⇒
  same_frame_or_grow (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem same_frame_or_grow_ignore_bind[simp]:
  same_frame_or_grow g ∧ same_frame_or_grow f ⇒
  same_frame_or_grow (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem same_frame_or_grow_handle[simp]:
  same_frame_or_grow f ∧ (∀e. same_frame_or_grow (h e)) ⇒
  same_frame_or_grow (handle f h)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem same_frame_or_grow_cond[simp]:
  same_frame_or_grow m1 ∧ same_frame_or_grow m2 ⇒
  same_frame_or_grow (if b then m1 else m2)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem same_frame_or_grow_case_option[simp]:
  same_frame_or_grow m_none ∧ (∀x. same_frame_or_grow (m_some x)) ⇒
  same_frame_or_grow
    (case opt of NONE => m_none | SOME x => m_some x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem same_frame_or_grow_case_sum[simp]:
  (∀x. same_frame_or_grow (f x)) ∧ (∀y. same_frame_or_grow (g y)) ⇒
  same_frame_or_grow
    (case sm of INL x => f x | INR y => g y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem same_frame_or_grow_case_pair[simp]:
  (∀x y. same_frame_or_grow (f x y)) ⇒
  same_frame_or_grow (case pr of (x, y) => f x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem same_frame_or_grow_let[simp]:
  (∀x. same_frame_or_grow (f x)) ⇒
  same_frame_or_grow (let x = v in f x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem same_frame_or_grow_uncurry[simp]:
  (∀x y. same_frame_or_grow (f x y)) ⇒
  same_frame_or_grow (UNCURRY f pr)
Proof
  cheat  (* SCAFFOLD *)
QED

(* ---------------- proceed_call / proceed_create grow ------------ *)

Theorem same_frame_or_grow_proceed_call[simp]:
  same_frame_or_grow
    (proceed_call op sender addr value aOff aSz code stipend outTo)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem same_frame_or_grow_proceed_create[simp]:
  same_frame_or_grow
    (proceed_create senderAddr addr value code gas)
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

Theorem same_frame_or_grow_eq_psf_or_grow_T:
  same_frame_or_grow m ⇔ psf_or_grow (λs. T) m
Proof
  cheat  (* SCAFFOLD *)
QED

(* ---------------- Composition rules ------------------- *)

Theorem psf_or_grow_bind:
  psf_or_grow p g ∧
  (∀x. psf_or_grow (p_cont x) (f x)) ∧
  (∀x s s'. g s = (INL x, s') ∧ p s ∧ s.contexts ≠ [] ⇒
            p_cont x s') ⇒
  psf_or_grow p (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_or_grow_ignore_bind:
  psf_or_grow p g ∧
  psf_or_grow p_cont f ∧
  (∀s x s'. g s = (INL x, s') ∧ p s ∧ s.contexts ≠ [] ⇒ p_cont s') ⇒
  psf_or_grow p (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_or_grow_cond[simp]:
  psf_or_grow p m1 ∧ psf_or_grow p m2 ⇒
  psf_or_grow p (if b then m1 else m2)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_or_grow_case_option[simp]:
  psf_or_grow p m_none ∧ (∀x. psf_or_grow p (m_some x)) ⇒
  psf_or_grow p (case opt of NONE => m_none | SOME x => m_some x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem psf_or_grow_let[simp]:
  (∀x. psf_or_grow p (f x)) ⇒
  psf_or_grow p (let x = v in f x)
Proof
  cheat  (* SCAFFOLD *)
QED

(* ---------------- Specialised getter-bind for get_callee -------- *)

Theorem psf_or_grow_bind_get_callee:
  (∀x. psf_or_grow (λs. p s ∧ x = (FST (HD s.contexts)).msgParams.callee)
                    (f x)) ⇒
  psf_or_grow p (bind get_callee f)
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

(* ---------------- step_call and step_create -------------------- *)

Theorem same_frame_or_grow_step_call[simp]:
  same_frame_or_grow (step_call op)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem same_frame_or_grow_step_create[simp]:
  same_frame_or_grow (step_create two)
Proof
  cheat  (* SCAFFOLD *)
QED

(* ---------------- Final same-frame theorems -------------------- *)

Theorem step_call_same_frame:
  outputTo_consistent s ∧
  step_call op s = (r, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  same_frame_rel s s'
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_create_same_frame:
  outputTo_consistent s ∧
  step_create two s = (r, s') ∧
  LENGTH s'.contexts = LENGTH s.contexts ⇒
  same_frame_rel s s'
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

(* The inner monad of step (before the outer handle) is composed of
   preserves_same_frame prefixes followed by a step_inst and
   inc_pc_or_jump. It satisfies same_frame_or_grow. *)
Theorem same_frame_or_grow_step_inner[simp]:
  same_frame_or_grow
    (do
       context <- get_current_context;
       case FLOOKUP context.msgParams.parsed context.pc of
       | SOME op => do step_inst op; inc_pc_or_jump op od
       | NONE =>
           if LENGTH context.msgParams.code ≤ context.pc then step_inst Stop
           else step_inst Invalid
     od)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem same_frame_or_grow_step_inner_named[simp]:
  same_frame_or_grow step_inner
Proof
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
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
  cheat  (* SCAFFOLD *)
QED

Theorem proceed_call_returns_inl:
  s.contexts ≠ [] ∧ ¬fIN c precompile_addresses ∧
  proceed_call a b c d e f g h i s = (r, s') ⇒
  ISL r
Proof
  cheat  (* SCAFFOLD *)
QED

(* step_create never INR-grows. Use same_frame_or_grow_step_create:
   either same-frame (length preserved), or grew ≥ 1. In the grow case,
   all non-proceed_create branches don't grow, so we must have reached
   proceed_create. proceed_create returns INL, so the outer result is
   INL too, contradicting our INR hypothesis.

   We formalise this as: step_create, in the grow case, returns INL. *)
(* step_create grown result must be INL: every primitive in step_create's
   bind chain either preserves_same_frame (no grow) or is
   proceed_create (returns INL). So grown + INR is impossible.
   Formalised below as `length_or_inl_grow` predicate with
   composition rules. *)
(* Helper: abort_unuse/abort_create_exists both preserve length.
   They are each a sequence of primitive effects none of which push
   or pop contexts. *)
Theorem abort_unuse_length:
  s.contexts ≠ [] ∧ abort_unuse n s = (r, s') ⇒
  LENGTH s'.contexts = LENGTH s.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem abort_create_exists_length:
  s.contexts ≠ [] ∧ abort_create_exists a s = (r, s') ⇒
  LENGTH s'.contexts = LENGTH s.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

(* ================================================================ *)
(* grown_is_inl: if a monad grows the context stack, the result is
   INL. This property composes nicely through bind because it's
   "monotone" (once grown, INL is determined).

   Key insight: we need a *combined* property with length preservation
   too. The predicate length_or_inl_grow tracks: the monad either
   strictly preserves length, or grows length and returns INL. *)
(* ================================================================ *)

(* Precondition-free length preservation: m preserves contexts length
   whenever the input contexts are non-empty. (For empty contexts,
   many primitives fail with Impossible, which we can treat as a
   special case if needed.) *)
Definition length_preserves_def:
  length_preserves (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ∧ s.contexts ≠ [] ⇒
             LENGTH s'.contexts = LENGTH s.contexts
End

Definition length_or_inl_grow_def:
  length_or_inl_grow (m: α execution) ⇔
    ∀s r s'. m s = (r, s') ∧ s.contexts ≠ [] ⇒
      LENGTH s'.contexts = LENGTH s.contexts ∨
      (LENGTH s'.contexts > LENGTH s.contexts ∧ ISL r)
End

Theorem length_preserves_imp_length_or_inl_grow:
  length_preserves m ⇒ length_or_inl_grow m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem length_preserves_of_preserves_same_frame[simp]:
  preserves_same_frame m ⇒ length_preserves m
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem length_or_inl_grow_of_length_preserves[simp]:
  length_preserves m ⇒ length_or_inl_grow m
Proof
  cheat  (* SCAFFOLD *)
QED

(* Composition through bind: g.length_preserves ensures f runs on
   state with same length as start; then f can either preserve or
   grow+INL, giving length_or_inl_grow for the bind. *)
Theorem length_or_inl_grow_bind_preserves_g:
  length_preserves g ∧
  (∀x. length_or_inl_grow (f x)) ⇒
  length_or_inl_grow (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem length_or_inl_grow_ignore_bind_preserves_g:
  length_preserves g ∧
  length_or_inl_grow f ⇒
  length_or_inl_grow (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem length_or_inl_grow_cond[simp]:
  length_or_inl_grow m1 ∧ length_or_inl_grow m2 ⇒
  length_or_inl_grow (if b then m1 else m2)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem length_or_inl_grow_let[simp]:
  (∀x. length_or_inl_grow (f x)) ⇒
  length_or_inl_grow (let x = v in f x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem length_or_inl_grow_case_option[simp]:
  length_or_inl_grow m_none ∧ (∀x. length_or_inl_grow (m_some x)) ⇒
  length_or_inl_grow (case opt of NONE => m_none | SOME x => m_some x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem length_preserves_case_sum[simp]:
  (∀x. length_preserves (m_inl x)) ∧ (∀y. length_preserves (m_inr y)) ⇒
  length_preserves (case v of INL x => m_inl x | INR y => m_inr y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem length_or_inl_grow_case_sum[simp]:
  (∀x. length_or_inl_grow (m_inl x)) ∧
  (∀y. length_or_inl_grow (m_inr y)) ⇒
  length_or_inl_grow (case v of INL x => m_inl x | INR y => m_inr y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem length_or_inl_grow_case_pair[simp]:
  (∀x y. length_or_inl_grow (m x y)) ⇒
  length_or_inl_grow (case p of (x, y) => m x y)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem length_preserves_case_pair[simp]:
  (∀x y. length_preserves (m x y)) ⇒
  length_preserves (case p of (x, y) => m x y)
Proof
  cheat  (* SCAFFOLD *)
QED

(* Composition for length_preserves *)
Theorem length_preserves_bind:
  length_preserves g ∧
  (∀x. length_preserves (f x)) ⇒
  length_preserves (bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem length_preserves_ignore_bind:
  length_preserves g ∧ length_preserves f ⇒
  length_preserves (ignore_bind g f)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem length_preserves_cond[simp]:
  length_preserves m1 ∧ length_preserves m2 ⇒
  length_preserves (if b then m1 else m2)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem length_preserves_case_option[simp]:
  length_preserves m_none ∧ (∀x. length_preserves (m_some x)) ⇒
  length_preserves (case opt of NONE => m_none | SOME x => m_some x)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem length_preserves_let[simp]:
  (∀x. length_preserves (f x)) ⇒
  length_preserves (let x = v in f x)
Proof
  cheat  (* SCAFFOLD *)
QED

(* proceed_create grows by 1 and returns INL. *)
Theorem length_or_inl_grow_proceed_create[simp]:
  length_or_inl_grow (proceed_create sa a v c g)
Proof
  cheat  (* SCAFFOLD *)
QED

(* abort_unuse and abort_create_exists are length_preserves. *)
Theorem length_preserves_abort_unuse[simp]:
  length_preserves (abort_unuse n)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem length_preserves_abort_create_exists[simp]:
  length_preserves (abort_create_exists a)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem length_or_inl_grow_step_create[simp]:
  length_or_inl_grow (step_create two)
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_create_grown_returns_inl:
  s.contexts ≠ [] ∧
  step_create two s = (r, s') ∧
  LENGTH s'.contexts ≥ LENGTH s.contexts + 1 ⇒
  ISL r
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_create_inr_no_grow:
  s.contexts ≠ [] ∧ step_create two s = (INR e, s') ⇒
  LENGTH s'.contexts = LENGTH s.contexts
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem step_inst_inr_grew_is_call_family:
  step_inst op s = (INR e, s') ∧
  LENGTH s'.contexts > LENGTH s.contexts ∧
  s.contexts ≠ [] ⇒
  op = Call ∨ op = CallCode ∨ op = DelegateCall ∨ op = StaticCall
Proof
  cheat  (* SCAFFOLD *)
QED

Theorem bind_length_preserves_imp_grow:
  length_preserves m ∧
  (∀x s r. f x s = (r,s') ∧ s.contexts ≠ [] ∧
           LENGTH s'.contexts > LENGTH s.contexts
     ⇒ LENGTH s'.contexts = LENGTH s.contexts + 1) ∧
  bind m f s = (r,s') ∧ s.contexts ≠ [] ∧
  LENGTH s'.contexts > LENGTH s.contexts
  ⇒
  LENGTH s'.contexts = LENGTH s.contexts + 1
Proof
  cheat  (* SCAFFOLD *)
QED

(* When step_call grows, it grows by exactly 1 (via proceed_call). *)
Theorem step_call_grows_by_exactly_one:
  s.contexts ≠ [] ∧ step_call op s = (r, s') ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  LENGTH s'.contexts = LENGTH s.contexts + 1
Proof
  cheat  (* SCAFFOLD *)
QED

(* When step_create grows, it grows by exactly 1 (via proceed_create). *)
Theorem step_create_grows_by_exactly_one:
  s.contexts ≠ [] ∧ step_create two s = (r, s') ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  LENGTH s'.contexts = LENGTH s.contexts + 1
Proof
  cheat  (* SCAFFOLD *)
QED

(* When the inner computation of step grows, it grows by exactly 1.
   This is because all growth paths go through step_call or step_create,
   which grow by exactly 1 via proceed_call/proceed_create. *)
Theorem step_inner_grows_by_exactly_one:
  s.contexts ≠ [] ∧
  (do
     context <- get_current_context;
     case FLOOKUP context.msgParams.parsed context.pc of
     | SOME op => do step_inst op; inc_pc_or_jump op od
     | NONE =>
         if LENGTH context.msgParams.code ≤ context.pc then step_inst Stop
         else step_inst Invalid
   od) s = (r, s') ∧
  LENGTH s'.contexts > LENGTH s.contexts ⇒
  LENGTH s'.contexts = LENGTH s.contexts + 1
Proof
  cheat  (* SCAFFOLD *)
QED


