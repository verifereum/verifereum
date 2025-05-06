open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2675Theory;
val () = new_theory "vfmTest2675";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2675") $ get_result_defs "vfmTestDefs2675";
val () = export_theory_no_docs ();
