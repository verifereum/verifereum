open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1108Theory;
val () = new_theory "vfmTest1108";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1108") $ get_result_defs "vfmTestDefs1108";
val () = export_theory_no_docs ();
