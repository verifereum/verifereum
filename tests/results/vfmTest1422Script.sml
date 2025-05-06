open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1422Theory;
val () = new_theory "vfmTest1422";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1422") $ get_result_defs "vfmTestDefs1422";
val () = export_theory_no_docs ();
