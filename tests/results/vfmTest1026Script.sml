open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1026Theory;
val () = new_theory "vfmTest1026";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1026") $ get_result_defs "vfmTestDefs1026";
val () = export_theory_no_docs ();
