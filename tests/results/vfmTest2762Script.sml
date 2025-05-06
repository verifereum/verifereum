open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2762Theory;
val () = new_theory "vfmTest2762";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2762") $ get_result_defs "vfmTestDefs2762";
val () = export_theory_no_docs ();
