open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs181Theory;
val () = new_theory "vfmStateTest181";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs181") $ get_result_defs "vfmStateTestDefs181";
val () = export_theory_no_docs ();
