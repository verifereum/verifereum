open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2308Theory;
val () = new_theory "vfmTest2308";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2308") $ get_result_defs "vfmTestDefs2308";
val () = export_theory_no_docs ();
