open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs091Theory;
val () = new_theory "vfmStateTest091";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs091";
val () = export_theory_no_docs ();
