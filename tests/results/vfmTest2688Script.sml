open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2688Theory;
val () = new_theory "vfmTest2688";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2688") $ get_result_defs "vfmTestDefs2688";
val () = export_theory_no_docs ();
