open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1513Theory;
val () = new_theory "vfmTest1513";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1513") $ get_result_defs "vfmTestDefs1513";
val () = export_theory_no_docs ();
