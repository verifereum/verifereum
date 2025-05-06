open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2152Theory;
val () = new_theory "vfmTest2152";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2152") $ get_result_defs "vfmTestDefs2152";
val () = export_theory_no_docs ();
