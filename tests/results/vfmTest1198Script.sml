open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1198Theory;
val () = new_theory "vfmTest1198";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1198") $ get_result_defs "vfmTestDefs1198";
val () = export_theory_no_docs ();
