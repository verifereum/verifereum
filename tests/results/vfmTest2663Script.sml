open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2663Theory;
val () = new_theory "vfmTest2663";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2663") $ get_result_defs "vfmTestDefs2663";
val () = export_theory_no_docs ();
