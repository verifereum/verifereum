open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1384Theory;
val () = new_theory "vfmTest1384";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1384") $ get_result_defs "vfmTestDefs1384";
val () = export_theory_no_docs ();
