open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0277Theory;
val () = new_theory "vfmTest0277";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0277") $ get_result_defs "vfmTestDefs0277";
val () = export_theory_no_docs ();
