open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1214Theory;
val () = new_theory "vfmTest1214";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1214") $ get_result_defs "vfmTestDefs1214";
val () = export_theory_no_docs ();
