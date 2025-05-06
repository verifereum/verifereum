open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2852Theory;
val () = new_theory "vfmTest2852";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2852") $ get_result_defs "vfmTestDefs2852";
val () = export_theory_no_docs ();
