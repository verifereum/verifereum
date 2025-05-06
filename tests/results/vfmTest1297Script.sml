open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1297Theory;
val () = new_theory "vfmTest1297";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1297") $ get_result_defs "vfmTestDefs1297";
val () = export_theory_no_docs ();
