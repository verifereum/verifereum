open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0343Theory;
val () = new_theory "vfmTest0343";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0343") $ get_result_defs "vfmTestDefs0343";
val () = export_theory_no_docs ();
