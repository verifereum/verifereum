open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1016Theory;
val () = new_theory "vfmTest1016";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1016") $ get_result_defs "vfmTestDefs1016";
val () = export_theory_no_docs ();
