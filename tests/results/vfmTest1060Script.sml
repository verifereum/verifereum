open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1060Theory;
val () = new_theory "vfmTest1060";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1060") $ get_result_defs "vfmTestDefs1060";
val () = export_theory_no_docs ();
