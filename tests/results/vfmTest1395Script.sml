open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1395Theory;
val () = new_theory "vfmTest1395";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1395") $ get_result_defs "vfmTestDefs1395";
val () = export_theory_no_docs ();
