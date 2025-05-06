open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1284Theory;
val () = new_theory "vfmTest1284";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1284") $ get_result_defs "vfmTestDefs1284";
val () = export_theory_no_docs ();
