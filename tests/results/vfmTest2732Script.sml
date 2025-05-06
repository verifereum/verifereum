open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2732Theory;
val () = new_theory "vfmTest2732";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2732") $ get_result_defs "vfmTestDefs2732";
val () = export_theory_no_docs ();
