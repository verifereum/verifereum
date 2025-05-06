open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1486Theory;
val () = new_theory "vfmTest1486";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1486") $ get_result_defs "vfmTestDefs1486";
val () = export_theory_no_docs ();
