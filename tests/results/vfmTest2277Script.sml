open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2277Theory;
val () = new_theory "vfmTest2277";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2277") $ get_result_defs "vfmTestDefs2277";
val () = export_theory_no_docs ();
