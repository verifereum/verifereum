open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1076Theory;
val () = new_theory "vfmTest1076";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1076") $ get_result_defs "vfmTestDefs1076";
val () = export_theory_no_docs ();
