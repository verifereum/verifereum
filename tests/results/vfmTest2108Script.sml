open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2108Theory;
val () = new_theory "vfmTest2108";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2108") $ get_result_defs "vfmTestDefs2108";
val () = export_theory_no_docs ();
