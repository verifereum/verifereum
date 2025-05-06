open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1158Theory;
val () = new_theory "vfmTest1158";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1158") $ get_result_defs "vfmTestDefs1158";
val () = export_theory_no_docs ();
