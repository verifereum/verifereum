open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs005Theory;
val () = new_theory "vfmStateTest005";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs005") $ get_result_defs "vfmStateTestDefs005";
val () = export_theory_no_docs ();
