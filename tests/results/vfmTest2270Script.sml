open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2270Theory;
val () = new_theory "vfmTest2270";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2270") $ get_result_defs "vfmTestDefs2270";
val () = export_theory_no_docs ();
