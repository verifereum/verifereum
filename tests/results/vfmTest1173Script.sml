open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1173Theory;
val () = new_theory "vfmTest1173";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1173") $ get_result_defs "vfmTestDefs1173";
val () = export_theory_no_docs ();
