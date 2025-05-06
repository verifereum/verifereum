open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1045Theory;
val () = new_theory "vfmTest1045";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1045") $ get_result_defs "vfmTestDefs1045";
val () = export_theory_no_docs ();
