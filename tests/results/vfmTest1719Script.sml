open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1719Theory;
val () = new_theory "vfmTest1719";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1719") $ get_result_defs "vfmTestDefs1719";
val () = export_theory_no_docs ();
