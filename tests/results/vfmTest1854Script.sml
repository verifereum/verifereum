open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1854Theory;
val () = new_theory "vfmTest1854";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1854") $ get_result_defs "vfmTestDefs1854";
val () = export_theory_no_docs ();
