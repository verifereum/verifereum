open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1069Theory;
val () = new_theory "vfmTest1069";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1069") $ get_result_defs "vfmTestDefs1069";
val () = export_theory_no_docs ();
