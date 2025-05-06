open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2355Theory;
val () = new_theory "vfmTest2355";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2355") $ get_result_defs "vfmTestDefs2355";
val () = export_theory_no_docs ();
