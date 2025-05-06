open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1081Theory;
val () = new_theory "vfmTest1081";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1081") $ get_result_defs "vfmTestDefs1081";
val () = export_theory_no_docs ();
