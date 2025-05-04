open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs060Theory;
val () = new_theory "vfmStateTest060";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs060";
val () = export_theory_no_docs ();
