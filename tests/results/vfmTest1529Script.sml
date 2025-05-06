open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1529Theory;
val () = new_theory "vfmTest1529";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1529") $ get_result_defs "vfmTestDefs1529";
val () = export_theory_no_docs ();
