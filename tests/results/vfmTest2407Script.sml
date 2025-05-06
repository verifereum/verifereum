open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2407Theory;
val () = new_theory "vfmTest2407";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2407") $ get_result_defs "vfmTestDefs2407";
val () = export_theory_no_docs ();
