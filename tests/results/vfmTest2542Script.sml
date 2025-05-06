open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2542Theory;
val () = new_theory "vfmTest2542";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2542") $ get_result_defs "vfmTestDefs2542";
val () = export_theory_no_docs ();
