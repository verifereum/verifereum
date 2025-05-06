open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1187Theory;
val () = new_theory "vfmTest1187";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1187") $ get_result_defs "vfmTestDefs1187";
val () = export_theory_no_docs ();
