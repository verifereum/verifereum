open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1020Theory;
val () = new_theory "vfmTest1020";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1020") $ get_result_defs "vfmTestDefs1020";
val () = export_theory_no_docs ();
