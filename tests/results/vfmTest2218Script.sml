open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2218Theory;
val () = new_theory "vfmTest2218";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2218") $ get_result_defs "vfmTestDefs2218";
val () = export_theory_no_docs ();
