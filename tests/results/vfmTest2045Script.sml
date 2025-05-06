open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2045Theory;
val () = new_theory "vfmTest2045";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2045") $ get_result_defs "vfmTestDefs2045";
val () = export_theory_no_docs ();
