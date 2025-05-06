open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1287Theory;
val () = new_theory "vfmTest1287";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1287") $ get_result_defs "vfmTestDefs1287";
val () = export_theory_no_docs ();
