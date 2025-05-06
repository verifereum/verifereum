open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1577Theory;
val () = new_theory "vfmTest1577";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1577") $ get_result_defs "vfmTestDefs1577";
val () = export_theory_no_docs ();
