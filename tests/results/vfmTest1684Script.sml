open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1684Theory;
val () = new_theory "vfmTest1684";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1684") $ get_result_defs "vfmTestDefs1684";
val () = export_theory_no_docs ();
