open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2623Theory;
val () = new_theory "vfmTest2623";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2623") $ get_result_defs "vfmTestDefs2623";
val () = export_theory_no_docs ();
