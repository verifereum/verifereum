open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2456Theory;
val () = new_theory "vfmTest2456";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2456") $ get_result_defs "vfmTestDefs2456";
val () = export_theory_no_docs ();
