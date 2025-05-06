open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1005Theory;
val () = new_theory "vfmTest1005";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1005") $ get_result_defs "vfmTestDefs1005";
val () = export_theory_no_docs ();
