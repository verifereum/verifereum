open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1457Theory;
val () = new_theory "vfmTest1457";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1457") $ get_result_defs "vfmTestDefs1457";
val () = export_theory_no_docs ();
