open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1209Theory;
val () = new_theory "vfmTest1209";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1209") $ get_result_defs "vfmTestDefs1209";
val () = export_theory_no_docs ();
