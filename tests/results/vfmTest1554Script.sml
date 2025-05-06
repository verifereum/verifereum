open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1554Theory;
val () = new_theory "vfmTest1554";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1554") $ get_result_defs "vfmTestDefs1554";
val () = export_theory_no_docs ();
