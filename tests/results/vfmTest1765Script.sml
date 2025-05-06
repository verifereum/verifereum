open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1765Theory;
val () = new_theory "vfmTest1765";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1765") $ get_result_defs "vfmTestDefs1765";
val () = export_theory_no_docs ();
