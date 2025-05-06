open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2331Theory;
val () = new_theory "vfmTest2331";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2331") $ get_result_defs "vfmTestDefs2331";
val () = export_theory_no_docs ();
