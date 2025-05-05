open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs134Theory;
val () = new_theory "vfmStateTest134";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs134") $ get_result_defs "vfmStateTestDefs134";
val () = export_theory_no_docs ();
