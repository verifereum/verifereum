open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2083Theory;
val () = new_theory "vfmTest2083";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2083") $ get_result_defs "vfmTestDefs2083";
val () = export_theory_no_docs ();
