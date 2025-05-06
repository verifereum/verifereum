open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2499Theory;
val () = new_theory "vfmTest2499";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2499") $ get_result_defs "vfmTestDefs2499";
val () = export_theory_no_docs ();
