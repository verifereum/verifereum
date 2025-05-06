open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2747Theory;
val () = new_theory "vfmTest2747";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2747") $ get_result_defs "vfmTestDefs2747";
val () = export_theory_no_docs ();
