open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0705Theory;
val () = new_theory "vfmTest0705";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0705") $ get_result_defs "vfmTestDefs0705";
val () = export_theory_no_docs ();
