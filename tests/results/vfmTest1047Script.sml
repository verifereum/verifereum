open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1047Theory;
val () = new_theory "vfmTest1047";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1047") $ get_result_defs "vfmTestDefs1047";
val () = export_theory_no_docs ();
