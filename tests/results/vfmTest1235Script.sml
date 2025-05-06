open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1235Theory;
val () = new_theory "vfmTest1235";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1235") $ get_result_defs "vfmTestDefs1235";
val () = export_theory_no_docs ();
