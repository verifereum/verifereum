open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs122Theory;
val () = new_theory "vfmStateTest122";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs122";
val () = export_theory_no_docs ();
