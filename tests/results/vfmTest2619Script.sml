open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2619Theory;
val () = new_theory "vfmTest2619";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2619") $ get_result_defs "vfmTestDefs2619";
val () = export_theory_no_docs ();
