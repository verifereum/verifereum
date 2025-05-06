open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2343Theory;
val () = new_theory "vfmTest2343";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2343") $ get_result_defs "vfmTestDefs2343";
val () = export_theory_no_docs ();
