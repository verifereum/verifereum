open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1953Theory;
val () = new_theory "vfmTest1953";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1953") $ get_result_defs "vfmTestDefs1953";
val () = export_theory_no_docs ();
