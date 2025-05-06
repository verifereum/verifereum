open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2372Theory;
val () = new_theory "vfmTest2372";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2372") $ get_result_defs "vfmTestDefs2372";
val () = export_theory_no_docs ();
