open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2422Theory;
val () = new_theory "vfmTest2422";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2422") $ get_result_defs "vfmTestDefs2422";
val () = export_theory_no_docs ();
