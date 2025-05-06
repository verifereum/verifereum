open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2527Theory;
val () = new_theory "vfmTest2527";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2527") $ get_result_defs "vfmTestDefs2527";
val () = export_theory_no_docs ();
