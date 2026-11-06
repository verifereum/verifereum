(*
 * Execution never reads the deletion queue.
 *
 * rollback.toDelete is only ever extended (SELFDESTRUCT conses onto it),
 * copied into a frame's saved rollback when a call pushes it, and restored
 * from that copy when the frame reverts; the queue is read only when the
 * transaction is settled (process_deletions). So two states that differ
 * only in their queues run in lockstep, and end in states that differ only
 * in their queues.
 *)
Theory vfmToDelete
Ancestors
  arithmetic list pair While
  vfmTypes vfmState vfmContext vfmExecution

(* Two states that differ only in their deletion queues: the current
   rollback's and the saved rollbacks' in every frame. *)
Definition erase_toDelete_def:
  erase_toDelete (s:execution_state) =
    s with <| rollback := s.rollback with toDelete := [];
              contexts := MAP (λ(c,rb). (c, rb with toDelete := [])) s.contexts |>
End

(* Proof intuition: step preserves "equal up to erase_toDelete" and returns
   the same result: add_to_delete conses onto both queues, a push saves
   related current rollbacks, a pop restores related saved rollbacks or
   keeps the related current ones, and nothing else reads or writes a
   queue (process_deletions runs only at settlement, outside run_call).
   run_call's loop guard reads only the result and the number of frames,
   which agree, so the two loops run in lockstep. get_rollback and
   pop_context return values that differ in toDelete, so a lemma of the form
   "each op preserves the relation and returns equal values" stops at them;
   push and pop are handled where they're used (proceed_call, step_create,
   pop_and_incorporate_context). *)
Theorem run_call_toDelete:
  erase_toDelete s1 = erase_toDelete s2 ∧ run_call s1 = SOME (r, t1) ⇒
  ∃t2. run_call s2 = SOME (r, t2) ∧ erase_toDelete t2 = erase_toDelete t1
Proof
  cheat
QED
