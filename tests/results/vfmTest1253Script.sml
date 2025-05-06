open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1253Theory;
val () = new_theory "vfmTest1253";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1253") $ get_result_defs "vfmTestDefs1253";
val () = export_theory_no_docs ();
