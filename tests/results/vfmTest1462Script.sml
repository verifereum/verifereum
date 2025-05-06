open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1462Theory;
val () = new_theory "vfmTest1462";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1462") $ get_result_defs "vfmTestDefs1462";
val () = export_theory_no_docs ();
