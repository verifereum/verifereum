open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2423Theory;
val () = new_theory "vfmTest2423";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2423") $ get_result_defs "vfmTestDefs2423";
val () = export_theory_no_docs ();
