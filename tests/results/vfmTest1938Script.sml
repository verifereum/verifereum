open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1938Theory;
val () = new_theory "vfmTest1938";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1938") $ get_result_defs "vfmTestDefs1938";
val () = export_theory_no_docs ();
