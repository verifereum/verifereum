open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2729Theory;
val () = new_theory "vfmTest2729";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2729") $ get_result_defs "vfmTestDefs2729";
val () = export_theory_no_docs ();
