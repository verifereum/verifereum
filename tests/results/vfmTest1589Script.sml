open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1589Theory;
val () = new_theory "vfmTest1589";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1589") $ get_result_defs "vfmTestDefs1589";
val () = export_theory_no_docs ();
