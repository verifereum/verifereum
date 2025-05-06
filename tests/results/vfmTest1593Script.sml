open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1593Theory;
val () = new_theory "vfmTest1593";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1593") $ get_result_defs "vfmTestDefs1593";
val () = export_theory_no_docs ();
