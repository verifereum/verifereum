open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1025Theory;
val () = new_theory "vfmTest1025";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1025") $ get_result_defs "vfmTestDefs1025";
val () = export_theory_no_docs ();
