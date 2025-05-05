open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs204Theory;
val () = new_theory "vfmStateTest204";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs204") $ get_result_defs "vfmStateTestDefs204";
val () = export_theory_no_docs ();
