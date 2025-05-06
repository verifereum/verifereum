open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1138Theory;
val () = new_theory "vfmTest1138";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1138") $ get_result_defs "vfmTestDefs1138";
val () = export_theory_no_docs ();
