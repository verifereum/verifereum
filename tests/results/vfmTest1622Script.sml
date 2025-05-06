open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1622Theory;
val () = new_theory "vfmTest1622";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1622") $ get_result_defs "vfmTestDefs1622";
val () = export_theory_no_docs ();
