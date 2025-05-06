open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2573Theory;
val () = new_theory "vfmTest2573";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2573") $ get_result_defs "vfmTestDefs2573";
val () = export_theory_no_docs ();
