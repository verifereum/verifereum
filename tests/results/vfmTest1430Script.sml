open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1430Theory;
val () = new_theory "vfmTest1430";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1430") $ get_result_defs "vfmTestDefs1430";
val () = export_theory_no_docs ();
