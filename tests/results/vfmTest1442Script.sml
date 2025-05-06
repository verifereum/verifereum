open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1442Theory;
val () = new_theory "vfmTest1442";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1442") $ get_result_defs "vfmTestDefs1442";
val () = export_theory_no_docs ();
