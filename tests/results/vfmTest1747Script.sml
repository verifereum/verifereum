open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1747Theory;
val () = new_theory "vfmTest1747";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1747") $ get_result_defs "vfmTestDefs1747";
val () = export_theory_no_docs ();
