open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1729Theory;
val () = new_theory "vfmTest1729";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1729") $ get_result_defs "vfmTestDefs1729";
val () = export_theory_no_docs ();
