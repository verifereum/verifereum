open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1972Theory;
val () = new_theory "vfmTest1972";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1972") $ get_result_defs "vfmTestDefs1972";
val () = export_theory_no_docs ();
