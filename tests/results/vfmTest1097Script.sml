open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1097Theory;
val () = new_theory "vfmTest1097";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1097") $ get_result_defs "vfmTestDefs1097";
val () = export_theory_no_docs ();
