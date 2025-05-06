open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1663Theory;
val () = new_theory "vfmTest1663";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1663") $ get_result_defs "vfmTestDefs1663";
val () = export_theory_no_docs ();
