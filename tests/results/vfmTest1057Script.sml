open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1057Theory;
val () = new_theory "vfmTest1057";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1057") $ get_result_defs "vfmTestDefs1057";
val () = export_theory_no_docs ();
