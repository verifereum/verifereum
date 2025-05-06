open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1436Theory;
val () = new_theory "vfmTest1436";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1436") $ get_result_defs "vfmTestDefs1436";
val () = export_theory_no_docs ();
