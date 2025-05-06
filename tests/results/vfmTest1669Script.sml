open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1669Theory;
val () = new_theory "vfmTest1669";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1669") $ get_result_defs "vfmTestDefs1669";
val () = export_theory_no_docs ();
