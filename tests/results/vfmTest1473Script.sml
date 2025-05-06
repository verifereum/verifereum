open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1473Theory;
val () = new_theory "vfmTest1473";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1473") $ get_result_defs "vfmTestDefs1473";
val () = export_theory_no_docs ();
