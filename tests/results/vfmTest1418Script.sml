open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1418Theory;
val () = new_theory "vfmTest1418";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1418") $ get_result_defs "vfmTestDefs1418";
val () = export_theory_no_docs ();
