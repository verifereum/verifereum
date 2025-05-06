open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2781Theory;
val () = new_theory "vfmTest2781";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2781") $ get_result_defs "vfmTestDefs2781";
val () = export_theory_no_docs ();
