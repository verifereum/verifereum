open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1382Theory;
val () = new_theory "vfmTest1382";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1382") $ get_result_defs "vfmTestDefs1382";
val () = export_theory_no_docs ();
