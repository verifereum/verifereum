open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1156Theory;
val () = new_theory "vfmTest1156";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1156") $ get_result_defs "vfmTestDefs1156";
val () = export_theory_no_docs ();
