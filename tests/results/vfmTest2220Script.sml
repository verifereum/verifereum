open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2220Theory;
val () = new_theory "vfmTest2220";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2220") $ get_result_defs "vfmTestDefs2220";
val () = export_theory_no_docs ();
