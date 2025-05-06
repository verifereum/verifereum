open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1046Theory;
val () = new_theory "vfmTest1046";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1046") $ get_result_defs "vfmTestDefs1046";
val () = export_theory_no_docs ();
