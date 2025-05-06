open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1412Theory;
val () = new_theory "vfmTest1412";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1412") $ get_result_defs "vfmTestDefs1412";
val () = export_theory_no_docs ();
