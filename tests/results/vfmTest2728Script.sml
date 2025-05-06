open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2728Theory;
val () = new_theory "vfmTest2728";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2728") $ get_result_defs "vfmTestDefs2728";
val () = export_theory_no_docs ();
