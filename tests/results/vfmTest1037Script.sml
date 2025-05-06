open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1037Theory;
val () = new_theory "vfmTest1037";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1037") $ get_result_defs "vfmTestDefs1037";
val () = export_theory_no_docs ();
