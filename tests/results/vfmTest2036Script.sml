open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2036Theory;
val () = new_theory "vfmTest2036";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2036") $ get_result_defs "vfmTestDefs2036";
val () = export_theory_no_docs ();
