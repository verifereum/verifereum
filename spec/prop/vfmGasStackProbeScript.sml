Theory vfmGasStackProbe
Ancestors vfmSameFrame vfmExecutionProp

(* Witness that `same_frame_rel_preserves_gas_stack_ok` is false once a frame
   can refund state gas: the frames below the parent keep an `EL (SUC i)`
   that the credit moves.  The measure the shipped statement carries instead
   is the one that survives. *)
Theorem same_frame_rel_preserves_gas_stack_ok_counterexample:
  !s c p rb.
    let c0 = c with <| msgParams := c.msgParams with gasLimit := 0;
                       gasUsed := 0; stateGasSpilled := 0 |> in
    let p0 = p with gasUsed := 0 in
    let s0 = s with contexts := [(c0,rb);(p0,rb)] in
    let s1 = s with contexts := [(c0 with stateGasSpilled := 1,rb);(p0,rb)] in
    same_frame_rel s0 s1 /\ gas_stack_ok s0 /\
    (FST (HD s1.contexts)).gasUsed >= (FST (HD s0.contexts)).gasUsed /\
    ~gas_stack_ok s1
Proof
  simp[same_frame_rel_def, gas_stack_ok_def,
       unused_gas_def, frame_unused_gas_def] >>
  rpt gen_tac >> conj_tac
  >- (rpt strip_tac >> `i = 0` by decide_tac >> gvs[]) >>
  qexists_tac `0` >> simp[]
QED
