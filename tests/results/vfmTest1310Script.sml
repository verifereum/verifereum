open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1310Theory;
val () = new_theory "vfmTest1310";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1310") $ get_result_defs "vfmTestDefs1310";
val () = export_theory_no_docs ();
