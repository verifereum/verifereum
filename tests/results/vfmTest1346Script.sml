open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1346Theory;
val () = new_theory "vfmTest1346";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1346") $ get_result_defs "vfmTestDefs1346";
val () = export_theory_no_docs ();
