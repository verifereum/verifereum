open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1562Theory;
val () = new_theory "vfmTest1562";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1562") $ get_result_defs "vfmTestDefs1562";
val () = export_theory_no_docs ();
