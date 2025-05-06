open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2287Theory;
val () = new_theory "vfmTest2287";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2287") $ get_result_defs "vfmTestDefs2287";
val () = export_theory_no_docs ();
