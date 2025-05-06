open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1289Theory;
val () = new_theory "vfmTest1289";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1289") $ get_result_defs "vfmTestDefs1289";
val () = export_theory_no_docs ();
