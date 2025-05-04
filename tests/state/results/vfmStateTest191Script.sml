open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs191Theory;
val () = new_theory "vfmStateTest191";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs191";
val () = export_theory_no_docs ();
