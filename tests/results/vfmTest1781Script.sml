open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1781Theory;
val () = new_theory "vfmTest1781";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1781") $ get_result_defs "vfmTestDefs1781";
val () = export_theory_no_docs ();
