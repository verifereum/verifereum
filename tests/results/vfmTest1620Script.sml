open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1620Theory;
val () = new_theory "vfmTest1620";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1620") $ get_result_defs "vfmTestDefs1620";
val () = export_theory_no_docs ();
