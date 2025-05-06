open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1265Theory;
val () = new_theory "vfmTest1265";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1265") $ get_result_defs "vfmTestDefs1265";
val () = export_theory_no_docs ();
