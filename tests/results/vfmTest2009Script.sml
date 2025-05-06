open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2009Theory;
val () = new_theory "vfmTest2009";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2009") $ get_result_defs "vfmTestDefs2009";
val () = export_theory_no_docs ();
