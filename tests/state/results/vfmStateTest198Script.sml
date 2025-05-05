open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs198Theory;
val () = new_theory "vfmStateTest198";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs198") $ get_result_defs "vfmStateTestDefs198";
val () = export_theory_no_docs ();
