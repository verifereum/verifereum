open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs158Theory;
val () = new_theory "vfmStateTest158";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs158") $ get_result_defs "vfmStateTestDefs158";
val () = export_theory_no_docs ();
