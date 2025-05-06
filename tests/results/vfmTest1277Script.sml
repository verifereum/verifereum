open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1277Theory;
val () = new_theory "vfmTest1277";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1277") $ get_result_defs "vfmTestDefs1277";
val () = export_theory_no_docs ();
