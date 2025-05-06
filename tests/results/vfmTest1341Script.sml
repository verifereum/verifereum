open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1341Theory;
val () = new_theory "vfmTest1341";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1341") $ get_result_defs "vfmTestDefs1341";
val () = export_theory_no_docs ();
