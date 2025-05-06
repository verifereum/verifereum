open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1004Theory;
val () = new_theory "vfmTest1004";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1004") $ get_result_defs "vfmTestDefs1004";
val () = export_theory_no_docs ();
