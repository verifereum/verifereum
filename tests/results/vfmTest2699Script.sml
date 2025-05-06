open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2699Theory;
val () = new_theory "vfmTest2699";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2699") $ get_result_defs "vfmTestDefs2699";
val () = export_theory_no_docs ();
