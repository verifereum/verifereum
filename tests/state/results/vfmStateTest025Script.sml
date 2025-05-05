open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs025Theory;
val () = new_theory "vfmStateTest025";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs025") $ get_result_defs "vfmStateTestDefs025";
val () = export_theory_no_docs ();
