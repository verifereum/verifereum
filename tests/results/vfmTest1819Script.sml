open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1819Theory;
val () = new_theory "vfmTest1819";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1819") $ get_result_defs "vfmTestDefs1819";
val () = export_theory_no_docs ();
