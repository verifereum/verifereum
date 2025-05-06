open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1226Theory;
val () = new_theory "vfmTest1226";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1226") $ get_result_defs "vfmTestDefs1226";
val () = export_theory_no_docs ();
