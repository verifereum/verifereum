open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1377Theory;
val () = new_theory "vfmTest1377";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1377") $ get_result_defs "vfmTestDefs1377";
val () = export_theory_no_docs ();
