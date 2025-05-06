open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1483Theory;
val () = new_theory "vfmTest1483";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1483") $ get_result_defs "vfmTestDefs1483";
val () = export_theory_no_docs ();
