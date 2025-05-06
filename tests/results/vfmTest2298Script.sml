open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2298Theory;
val () = new_theory "vfmTest2298";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2298") $ get_result_defs "vfmTestDefs2298";
val () = export_theory_no_docs ();
