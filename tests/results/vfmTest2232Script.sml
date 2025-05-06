open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2232Theory;
val () = new_theory "vfmTest2232";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2232") $ get_result_defs "vfmTestDefs2232";
val () = export_theory_no_docs ();
