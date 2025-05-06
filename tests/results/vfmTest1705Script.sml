open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1705Theory;
val () = new_theory "vfmTest1705";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1705") $ get_result_defs "vfmTestDefs1705";
val () = export_theory_no_docs ();
