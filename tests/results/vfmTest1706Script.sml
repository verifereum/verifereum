open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1706Theory;
val () = new_theory "vfmTest1706";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1706") $ get_result_defs "vfmTestDefs1706";
val () = export_theory_no_docs ();
