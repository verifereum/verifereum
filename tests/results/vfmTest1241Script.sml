open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1241Theory;
val () = new_theory "vfmTest1241";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1241") $ get_result_defs "vfmTestDefs1241";
val () = export_theory_no_docs ();
