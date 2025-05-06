open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2384Theory;
val () = new_theory "vfmTest2384";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2384") $ get_result_defs "vfmTestDefs2384";
val () = export_theory_no_docs ();
