open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2508Theory;
val () = new_theory "vfmTest2508";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2508") $ get_result_defs "vfmTestDefs2508";
val () = export_theory_no_docs ();
