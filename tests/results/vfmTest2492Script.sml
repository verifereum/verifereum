open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2492Theory;
val () = new_theory "vfmTest2492";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2492") $ get_result_defs "vfmTestDefs2492";
val () = export_theory_no_docs ();
