open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1274Theory;
val () = new_theory "vfmTest1274";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1274") $ get_result_defs "vfmTestDefs1274";
val () = export_theory_no_docs ();
