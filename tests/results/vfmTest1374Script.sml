open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1374Theory;
val () = new_theory "vfmTest1374";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1374") $ get_result_defs "vfmTestDefs1374";
val () = export_theory_no_docs ();
