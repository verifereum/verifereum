open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1419Theory;
val () = new_theory "vfmTest1419";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1419") $ get_result_defs "vfmTestDefs1419";
val () = export_theory_no_docs ();
