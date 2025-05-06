open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1058Theory;
val () = new_theory "vfmTest1058";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1058") $ get_result_defs "vfmTestDefs1058";
val () = export_theory_no_docs ();
