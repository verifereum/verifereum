open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1009Theory;
val () = new_theory "vfmTest1009";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1009") $ get_result_defs "vfmTestDefs1009";
val () = export_theory_no_docs ();
