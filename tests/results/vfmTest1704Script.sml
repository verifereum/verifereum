open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1704Theory;
val () = new_theory "vfmTest1704";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1704") $ get_result_defs "vfmTestDefs1704";
val () = export_theory_no_docs ();
