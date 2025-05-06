open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1305Theory;
val () = new_theory "vfmTest1305";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1305") $ get_result_defs "vfmTestDefs1305";
val () = export_theory_no_docs ();
