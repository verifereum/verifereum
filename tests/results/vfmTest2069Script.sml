open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2069Theory;
val () = new_theory "vfmTest2069";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2069") $ get_result_defs "vfmTestDefs2069";
val () = export_theory_no_docs ();
