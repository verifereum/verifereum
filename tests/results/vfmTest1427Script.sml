open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1427Theory;
val () = new_theory "vfmTest1427";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1427") $ get_result_defs "vfmTestDefs1427";
val () = export_theory_no_docs ();
