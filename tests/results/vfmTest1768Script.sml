open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1768Theory;
val () = new_theory "vfmTest1768";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1768") $ get_result_defs "vfmTestDefs1768";
val () = export_theory_no_docs ();
