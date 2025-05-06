open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1375Theory;
val () = new_theory "vfmTest1375";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1375") $ get_result_defs "vfmTestDefs1375";
val () = export_theory_no_docs ();
