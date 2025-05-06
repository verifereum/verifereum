open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2005Theory;
val () = new_theory "vfmTest2005";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2005") $ get_result_defs "vfmTestDefs2005";
val () = export_theory_no_docs ();
