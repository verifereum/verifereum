open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2324Theory;
val () = new_theory "vfmTest2324";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2324") $ get_result_defs "vfmTestDefs2324";
val () = export_theory_no_docs ();
