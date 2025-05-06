open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1542Theory;
val () = new_theory "vfmTest1542";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1542") $ get_result_defs "vfmTestDefs1542";
val () = export_theory_no_docs ();
