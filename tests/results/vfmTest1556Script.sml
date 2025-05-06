open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1556Theory;
val () = new_theory "vfmTest1556";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1556") $ get_result_defs "vfmTestDefs1556";
val () = export_theory_no_docs ();
