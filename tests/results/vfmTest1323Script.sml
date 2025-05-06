open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1323Theory;
val () = new_theory "vfmTest1323";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1323") $ get_result_defs "vfmTestDefs1323";
val () = export_theory_no_docs ();
