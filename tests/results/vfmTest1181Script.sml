open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1181Theory;
val () = new_theory "vfmTest1181";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1181") $ get_result_defs "vfmTestDefs1181";
val () = export_theory_no_docs ();
