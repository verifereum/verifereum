open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1121Theory;
val () = new_theory "vfmTest1121";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1121") $ get_result_defs "vfmTestDefs1121";
val () = export_theory_no_docs ();
