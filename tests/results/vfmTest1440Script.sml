open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1440Theory;
val () = new_theory "vfmTest1440";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1440") $ get_result_defs "vfmTestDefs1440";
val () = export_theory_no_docs ();
