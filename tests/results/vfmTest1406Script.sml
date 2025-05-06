open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1406Theory;
val () = new_theory "vfmTest1406";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1406") $ get_result_defs "vfmTestDefs1406";
val () = export_theory_no_docs ();
