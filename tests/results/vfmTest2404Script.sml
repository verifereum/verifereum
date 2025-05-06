open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2404Theory;
val () = new_theory "vfmTest2404";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2404") $ get_result_defs "vfmTestDefs2404";
val () = export_theory_no_docs ();
