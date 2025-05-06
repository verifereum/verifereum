open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0335Theory;
val () = new_theory "vfmTest0335";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0335") $ get_result_defs "vfmTestDefs0335";
val () = export_theory_no_docs ();
