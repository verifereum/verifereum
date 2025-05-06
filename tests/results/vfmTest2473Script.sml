open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2473Theory;
val () = new_theory "vfmTest2473";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2473") $ get_result_defs "vfmTestDefs2473";
val () = export_theory_no_docs ();
