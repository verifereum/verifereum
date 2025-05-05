open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs004Theory;
val () = new_theory "vfmStateTest004";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs004") $ get_result_defs "vfmStateTestDefs004";
val () = export_theory_no_docs ();
