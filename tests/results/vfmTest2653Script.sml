open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2653Theory;
val () = new_theory "vfmTest2653";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2653") $ get_result_defs "vfmTestDefs2653";
val () = export_theory_no_docs ();
