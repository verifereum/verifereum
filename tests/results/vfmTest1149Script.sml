open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1149Theory;
val () = new_theory "vfmTest1149";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1149") $ get_result_defs "vfmTestDefs1149";
val () = export_theory_no_docs ();
