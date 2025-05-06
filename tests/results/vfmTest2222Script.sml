open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2222Theory;
val () = new_theory "vfmTest2222";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2222") $ get_result_defs "vfmTestDefs2222";
val () = export_theory_no_docs ();
