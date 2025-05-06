open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1322Theory;
val () = new_theory "vfmTest1322";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1322") $ get_result_defs "vfmTestDefs1322";
val () = export_theory_no_docs ();
