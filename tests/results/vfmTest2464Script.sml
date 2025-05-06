open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2464Theory;
val () = new_theory "vfmTest2464";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2464") $ get_result_defs "vfmTestDefs2464";
val () = export_theory_no_docs ();
