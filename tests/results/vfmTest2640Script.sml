open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2640Theory;
val () = new_theory "vfmTest2640";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2640") $ get_result_defs "vfmTestDefs2640";
val () = export_theory_no_docs ();
