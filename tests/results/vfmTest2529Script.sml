open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2529Theory;
val () = new_theory "vfmTest2529";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2529") $ get_result_defs "vfmTestDefs2529";
val () = export_theory_no_docs ();
