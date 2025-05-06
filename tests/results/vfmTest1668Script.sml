open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1668Theory;
val () = new_theory "vfmTest1668";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1668") $ get_result_defs "vfmTestDefs1668";
val () = export_theory_no_docs ();
