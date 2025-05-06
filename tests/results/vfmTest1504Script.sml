open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1504Theory;
val () = new_theory "vfmTest1504";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1504") $ get_result_defs "vfmTestDefs1504";
val () = export_theory_no_docs ();
