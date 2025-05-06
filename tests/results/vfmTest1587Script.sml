open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1587Theory;
val () = new_theory "vfmTest1587";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1587") $ get_result_defs "vfmTestDefs1587";
val () = export_theory_no_docs ();
