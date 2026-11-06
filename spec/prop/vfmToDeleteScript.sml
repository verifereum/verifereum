(*
 * Execution never reads the deletion queue.
 *
 * rollback.toDelete is only ever extended (SELFDESTRUCT conses onto it),
 * copied into a frame's saved rollback when a call pushes it, and restored
 * from that copy when the frame reverts; the queue is read only when the
 * transaction is settled (process_deletions). So a run started with a
 * different queue takes the same steps and ends in the same state, up to
 * the queue itself.
 *)
Theory vfmToDelete
Ancestors
  arithmetic list pair While
  vfmTypes vfmState vfmContext vfmExecution

(* Proof intuition: relate the two runs by "equal up to rollback.toDelete,
   and up to toDelete in the saved rollbacks of the frames the run pushed".
   step preserves the relation: add_to_delete conses onto both queues, a
   push saves the related current rollbacks, a pop restores related saved
   rollbacks or keeps the related current ones, and nothing else reads or
   writes the queue. The frames below the run's start are never popped by
   run_call, so their saved rollbacks stay equal. The length premise
   excludes a run that stops on an abort (vfm_abort, which handle_step
   reraises without popping) inside a frame it pushed: that frame's saved
   rollback would still hold the other queue. *)
Theorem run_call_toDelete:
  run_call (s with rollback := s.rollback with toDelete := X) = SOME (r, t) ∧
  LENGTH t.contexts ≤ LENGTH s.contexts ⇒
  ∃Y. run_call s = SOME (r, t with rollback := t.rollback with toDelete := Y)
Proof
  cheat
QED
