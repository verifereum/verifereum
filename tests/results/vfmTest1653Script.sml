open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1653Theory;
val () = new_theory "vfmTest1653";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1653") $ get_result_defs "vfmTestDefs1653";
val () = export_theory_no_docs ();
