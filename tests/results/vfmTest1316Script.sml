open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1316Theory;
val () = new_theory "vfmTest1316";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1316") $ get_result_defs "vfmTestDefs1316";
val () = export_theory_no_docs ();
