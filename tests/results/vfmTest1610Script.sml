open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1610Theory;
val () = new_theory "vfmTest1610";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1610") $ get_result_defs "vfmTestDefs1610";
val () = export_theory_no_docs ();
