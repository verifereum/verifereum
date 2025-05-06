open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1697Theory;
val () = new_theory "vfmTest1697";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1697") $ get_result_defs "vfmTestDefs1697";
val () = export_theory_no_docs ();
