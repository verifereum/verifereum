open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1517Theory;
val () = new_theory "vfmTest1517";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1517") $ get_result_defs "vfmTestDefs1517";
val () = export_theory_no_docs ();
