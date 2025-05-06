open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1408Theory;
val () = new_theory "vfmTest1408";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1408") $ get_result_defs "vfmTestDefs1408";
val () = export_theory_no_docs ();
