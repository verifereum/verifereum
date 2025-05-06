open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1390Theory;
val () = new_theory "vfmTest1390";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1390") $ get_result_defs "vfmTestDefs1390";
val () = export_theory_no_docs ();
