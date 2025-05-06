open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2504Theory;
val () = new_theory "vfmTest2504";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2504") $ get_result_defs "vfmTestDefs2504";
val () = export_theory_no_docs ();
