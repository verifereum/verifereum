open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1258Theory;
val () = new_theory "vfmTest1258";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1258") $ get_result_defs "vfmTestDefs1258";
val () = export_theory_no_docs ();
