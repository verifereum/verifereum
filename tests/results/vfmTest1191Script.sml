open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1191Theory;
val () = new_theory "vfmTest1191";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1191") $ get_result_defs "vfmTestDefs1191";
val () = export_theory_no_docs ();
