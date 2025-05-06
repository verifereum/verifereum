open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1487Theory;
val () = new_theory "vfmTest1487";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1487") $ get_result_defs "vfmTestDefs1487";
val () = export_theory_no_docs ();
