open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2310Theory;
val () = new_theory "vfmTest2310";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2310") $ get_result_defs "vfmTestDefs2310";
val () = export_theory_no_docs ();
