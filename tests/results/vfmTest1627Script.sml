open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1627Theory;
val () = new_theory "vfmTest1627";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1627") $ get_result_defs "vfmTestDefs1627";
val () = export_theory_no_docs ();
