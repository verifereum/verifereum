open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1089Theory;
val () = new_theory "vfmTest1089";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1089") $ get_result_defs "vfmTestDefs1089";
val () = export_theory_no_docs ();
