open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2349Theory;
val () = new_theory "vfmTest2349";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2349") $ get_result_defs "vfmTestDefs2349";
val () = export_theory_no_docs ();
