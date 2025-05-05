open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs196Theory;
val () = new_theory "vfmStateTest196";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs196") $ get_result_defs "vfmStateTestDefs196";
val () = export_theory_no_docs ();
