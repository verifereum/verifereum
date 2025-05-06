open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1356Theory;
val () = new_theory "vfmTest1356";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1356") $ get_result_defs "vfmTestDefs1356";
val () = export_theory_no_docs ();
