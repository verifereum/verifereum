open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1299Theory;
val () = new_theory "vfmTest1299";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1299") $ get_result_defs "vfmTestDefs1299";
val () = export_theory_no_docs ();
