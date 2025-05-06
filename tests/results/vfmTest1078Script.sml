open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1078Theory;
val () = new_theory "vfmTest1078";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1078") $ get_result_defs "vfmTestDefs1078";
val () = export_theory_no_docs ();
