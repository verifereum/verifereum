open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1197Theory;
val () = new_theory "vfmTest1197";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1197") $ get_result_defs "vfmTestDefs1197";
val () = export_theory_no_docs ();
