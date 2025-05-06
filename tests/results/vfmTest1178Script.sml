open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1178Theory;
val () = new_theory "vfmTest1178";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1178") $ get_result_defs "vfmTestDefs1178";
val () = export_theory_no_docs ();
