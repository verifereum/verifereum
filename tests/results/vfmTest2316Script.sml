open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2316Theory;
val () = new_theory "vfmTest2316";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2316") $ get_result_defs "vfmTestDefs2316";
val () = export_theory_no_docs ();
