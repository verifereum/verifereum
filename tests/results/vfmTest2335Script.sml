open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2335Theory;
val () = new_theory "vfmTest2335";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2335") $ get_result_defs "vfmTestDefs2335";
val () = export_theory_no_docs ();
