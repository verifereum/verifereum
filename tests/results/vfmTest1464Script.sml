open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1464Theory;
val () = new_theory "vfmTest1464";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1464") $ get_result_defs "vfmTestDefs1464";
val () = export_theory_no_docs ();
