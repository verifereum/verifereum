open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1751Theory;
val () = new_theory "vfmTest1751";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1751") $ get_result_defs "vfmTestDefs1751";
val () = export_theory_no_docs ();
