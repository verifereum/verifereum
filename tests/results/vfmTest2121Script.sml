open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2121Theory;
val () = new_theory "vfmTest2121";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2121") $ get_result_defs "vfmTestDefs2121";
val () = export_theory_no_docs ();
