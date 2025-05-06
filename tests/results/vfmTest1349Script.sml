open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1349Theory;
val () = new_theory "vfmTest1349";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1349") $ get_result_defs "vfmTestDefs1349";
val () = export_theory_no_docs ();
