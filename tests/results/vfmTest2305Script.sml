open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2305Theory;
val () = new_theory "vfmTest2305";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2305") $ get_result_defs "vfmTestDefs2305";
val () = export_theory_no_docs ();
