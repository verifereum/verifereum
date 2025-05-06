open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1497Theory;
val () = new_theory "vfmTest1497";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1497") $ get_result_defs "vfmTestDefs1497";
val () = export_theory_no_docs ();
