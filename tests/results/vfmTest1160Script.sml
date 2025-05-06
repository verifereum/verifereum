open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1160Theory;
val () = new_theory "vfmTest1160";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1160") $ get_result_defs "vfmTestDefs1160";
val () = export_theory_no_docs ();
