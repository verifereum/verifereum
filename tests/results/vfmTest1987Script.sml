open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1987Theory;
val () = new_theory "vfmTest1987";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1987") $ get_result_defs "vfmTestDefs1987";
val () = export_theory_no_docs ();
