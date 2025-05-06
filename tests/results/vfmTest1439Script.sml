open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1439Theory;
val () = new_theory "vfmTest1439";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1439") $ get_result_defs "vfmTestDefs1439";
val () = export_theory_no_docs ();
