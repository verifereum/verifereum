open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1597Theory;
val () = new_theory "vfmTest1597";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1597") $ get_result_defs "vfmTestDefs1597";
val () = export_theory_no_docs ();
