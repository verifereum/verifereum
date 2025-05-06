open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1588Theory;
val () = new_theory "vfmTest1588";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1588") $ get_result_defs "vfmTestDefs1588";
val () = export_theory_no_docs ();
