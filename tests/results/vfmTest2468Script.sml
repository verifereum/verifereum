open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2468Theory;
val () = new_theory "vfmTest2468";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2468") $ get_result_defs "vfmTestDefs2468";
val () = export_theory_no_docs ();
