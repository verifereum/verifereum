open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2651Theory;
val () = new_theory "vfmTest2651";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2651") $ get_result_defs "vfmTestDefs2651";
val () = export_theory_no_docs ();
