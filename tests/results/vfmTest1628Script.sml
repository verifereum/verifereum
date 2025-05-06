open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1628Theory;
val () = new_theory "vfmTest1628";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1628") $ get_result_defs "vfmTestDefs1628";
val () = export_theory_no_docs ();
