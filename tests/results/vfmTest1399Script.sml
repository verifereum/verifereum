open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1399Theory;
val () = new_theory "vfmTest1399";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1399") $ get_result_defs "vfmTestDefs1399";
val () = export_theory_no_docs ();
