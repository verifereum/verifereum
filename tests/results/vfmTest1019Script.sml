open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1019Theory;
val () = new_theory "vfmTest1019";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1019") $ get_result_defs "vfmTestDefs1019";
val () = export_theory_no_docs ();
