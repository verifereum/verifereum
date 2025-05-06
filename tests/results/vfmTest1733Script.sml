open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1733Theory;
val () = new_theory "vfmTest1733";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1733") $ get_result_defs "vfmTestDefs1733";
val () = export_theory_no_docs ();
