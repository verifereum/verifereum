open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1343Theory;
val () = new_theory "vfmTest1343";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1343") $ get_result_defs "vfmTestDefs1343";
val () = export_theory_no_docs ();
