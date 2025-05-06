open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2361Theory;
val () = new_theory "vfmTest2361";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2361") $ get_result_defs "vfmTestDefs2361";
val () = export_theory_no_docs ();
