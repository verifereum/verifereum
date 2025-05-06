open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1270Theory;
val () = new_theory "vfmTest1270";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1270") $ get_result_defs "vfmTestDefs1270";
val () = export_theory_no_docs ();
