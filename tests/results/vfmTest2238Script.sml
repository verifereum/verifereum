open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2238Theory;
val () = new_theory "vfmTest2238";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2238") $ get_result_defs "vfmTestDefs2238";
val () = export_theory_no_docs ();
