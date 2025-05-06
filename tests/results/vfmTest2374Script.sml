open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2374Theory;
val () = new_theory "vfmTest2374";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2374") $ get_result_defs "vfmTestDefs2374";
val () = export_theory_no_docs ();
