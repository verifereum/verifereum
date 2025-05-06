open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2268Theory;
val () = new_theory "vfmTest2268";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2268") $ get_result_defs "vfmTestDefs2268";
val () = export_theory_no_docs ();
