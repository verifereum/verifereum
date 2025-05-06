open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2278Theory;
val () = new_theory "vfmTest2278";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2278") $ get_result_defs "vfmTestDefs2278";
val () = export_theory_no_docs ();
