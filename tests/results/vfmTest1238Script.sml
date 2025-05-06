open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1238Theory;
val () = new_theory "vfmTest1238";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1238") $ get_result_defs "vfmTestDefs1238";
val () = export_theory_no_docs ();
