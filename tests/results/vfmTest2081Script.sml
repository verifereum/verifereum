open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2081Theory;
val () = new_theory "vfmTest2081";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2081") $ get_result_defs "vfmTestDefs2081";
val () = export_theory_no_docs ();
