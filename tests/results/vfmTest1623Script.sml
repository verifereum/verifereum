open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1623Theory;
val () = new_theory "vfmTest1623";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1623") $ get_result_defs "vfmTestDefs1623";
val () = export_theory_no_docs ();
