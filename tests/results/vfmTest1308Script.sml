open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1308Theory;
val () = new_theory "vfmTest1308";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1308") $ get_result_defs "vfmTestDefs1308";
val () = export_theory_no_docs ();
