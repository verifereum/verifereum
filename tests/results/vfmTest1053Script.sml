open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1053Theory;
val () = new_theory "vfmTest1053";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1053") $ get_result_defs "vfmTestDefs1053";
val () = export_theory_no_docs ();
