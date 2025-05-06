open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2705Theory;
val () = new_theory "vfmTest2705";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2705") $ get_result_defs "vfmTestDefs2705";
val () = export_theory_no_docs ();
