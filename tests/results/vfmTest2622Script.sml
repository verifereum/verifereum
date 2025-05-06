open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2622Theory;
val () = new_theory "vfmTest2622";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2622") $ get_result_defs "vfmTestDefs2622";
val () = export_theory_no_docs ();
