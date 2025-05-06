open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2733Theory;
val () = new_theory "vfmTest2733";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2733") $ get_result_defs "vfmTestDefs2733";
val () = export_theory_no_docs ();
