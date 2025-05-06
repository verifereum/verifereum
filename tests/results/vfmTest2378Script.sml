open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2378Theory;
val () = new_theory "vfmTest2378";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2378") $ get_result_defs "vfmTestDefs2378";
val () = export_theory_no_docs ();
