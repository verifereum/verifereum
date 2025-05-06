open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1339Theory;
val () = new_theory "vfmTest1339";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1339") $ get_result_defs "vfmTestDefs1339";
val () = export_theory_no_docs ();
