open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1492Theory;
val () = new_theory "vfmTest1492";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1492") $ get_result_defs "vfmTestDefs1492";
val () = export_theory_no_docs ();
