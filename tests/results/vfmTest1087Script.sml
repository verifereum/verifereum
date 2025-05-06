open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1087Theory;
val () = new_theory "vfmTest1087";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1087") $ get_result_defs "vfmTestDefs1087";
val () = export_theory_no_docs ();
