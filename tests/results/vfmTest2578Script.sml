open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2578Theory;
val () = new_theory "vfmTest2578";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2578") $ get_result_defs "vfmTestDefs2578";
val () = export_theory_no_docs ();
