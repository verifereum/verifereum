open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1082Theory;
val () = new_theory "vfmTest1082";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1082") $ get_result_defs "vfmTestDefs1082";
val () = export_theory_no_docs ();
