open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs160Theory;
val () = new_theory "vfmStateTest160";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs160";
val () = export_theory_no_docs ();
