open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1434Theory;
val () = new_theory "vfmTest1434";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1434") $ get_result_defs "vfmTestDefs1434";
val () = export_theory_no_docs ();
