open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2181Theory;
val () = new_theory "vfmTest2181";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2181") $ get_result_defs "vfmTestDefs2181";
val () = export_theory_no_docs ();
