open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1803Theory;
val () = new_theory "vfmTest1803";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1803") $ get_result_defs "vfmTestDefs1803";
val () = export_theory_no_docs ();
