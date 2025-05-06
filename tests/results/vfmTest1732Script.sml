open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1732Theory;
val () = new_theory "vfmTest1732";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1732") $ get_result_defs "vfmTestDefs1732";
val () = export_theory_no_docs ();
