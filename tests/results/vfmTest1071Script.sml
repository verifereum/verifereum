open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1071Theory;
val () = new_theory "vfmTest1071";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1071") $ get_result_defs "vfmTestDefs1071";
val () = export_theory_no_docs ();
