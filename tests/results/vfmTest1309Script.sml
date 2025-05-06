open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1309Theory;
val () = new_theory "vfmTest1309";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1309") $ get_result_defs "vfmTestDefs1309";
val () = export_theory_no_docs ();
