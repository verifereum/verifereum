open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1134Theory;
val () = new_theory "vfmTest1134";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1134") $ get_result_defs "vfmTestDefs1134";
val () = export_theory_no_docs ();
