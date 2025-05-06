open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1599Theory;
val () = new_theory "vfmTest1599";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1599") $ get_result_defs "vfmTestDefs1599";
val () = export_theory_no_docs ();
