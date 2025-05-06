open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2497Theory;
val () = new_theory "vfmTest2497";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2497") $ get_result_defs "vfmTestDefs2497";
val () = export_theory_no_docs ();
