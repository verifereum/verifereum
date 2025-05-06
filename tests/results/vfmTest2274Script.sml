open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2274Theory;
val () = new_theory "vfmTest2274";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2274") $ get_result_defs "vfmTestDefs2274";
val () = export_theory_no_docs ();
