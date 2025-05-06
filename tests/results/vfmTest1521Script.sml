open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1521Theory;
val () = new_theory "vfmTest1521";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1521") $ get_result_defs "vfmTestDefs1521";
val () = export_theory_no_docs ();
