open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1145Theory;
val () = new_theory "vfmTest1145";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1145") $ get_result_defs "vfmTestDefs1145";
val () = export_theory_no_docs ();
