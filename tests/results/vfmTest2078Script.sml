open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2078Theory;
val () = new_theory "vfmTest2078";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2078") $ get_result_defs "vfmTestDefs2078";
val () = export_theory_no_docs ();
