open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1378Theory;
val () = new_theory "vfmTest1378";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1378") $ get_result_defs "vfmTestDefs1378";
val () = export_theory_no_docs ();
