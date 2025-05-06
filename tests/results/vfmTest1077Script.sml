open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1077Theory;
val () = new_theory "vfmTest1077";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1077") $ get_result_defs "vfmTestDefs1077";
val () = export_theory_no_docs ();
