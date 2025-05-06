open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2876Theory;
val () = new_theory "vfmTest2876";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2876") $ get_result_defs "vfmTestDefs2876";
val () = export_theory_no_docs ();
