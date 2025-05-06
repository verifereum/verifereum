open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2408Theory;
val () = new_theory "vfmTest2408";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2408") $ get_result_defs "vfmTestDefs2408";
val () = export_theory_no_docs ();
