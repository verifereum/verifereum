open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1614Theory;
val () = new_theory "vfmTest1614";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1614") $ get_result_defs "vfmTestDefs1614";
val () = export_theory_no_docs ();
