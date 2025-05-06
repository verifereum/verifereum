open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1971Theory;
val () = new_theory "vfmTest1971";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1971") $ get_result_defs "vfmTestDefs1971";
val () = export_theory_no_docs ();
