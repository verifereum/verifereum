open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1505Theory;
val () = new_theory "vfmTest1505";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1505") $ get_result_defs "vfmTestDefs1505";
val () = export_theory_no_docs ();
