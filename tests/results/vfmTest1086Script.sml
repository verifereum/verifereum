open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1086Theory;
val () = new_theory "vfmTest1086";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1086") $ get_result_defs "vfmTestDefs1086";
val () = export_theory_no_docs ();
