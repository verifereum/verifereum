open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2579Theory;
val () = new_theory "vfmTest2579";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2579") $ get_result_defs "vfmTestDefs2579";
val () = export_theory_no_docs ();
