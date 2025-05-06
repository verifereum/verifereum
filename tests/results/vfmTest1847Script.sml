open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1847Theory;
val () = new_theory "vfmTest1847";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1847") $ get_result_defs "vfmTestDefs1847";
val () = export_theory_no_docs ();
