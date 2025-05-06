open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1041Theory;
val () = new_theory "vfmTest1041";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1041") $ get_result_defs "vfmTestDefs1041";
val () = export_theory_no_docs ();
