open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1358Theory;
val () = new_theory "vfmTest1358";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1358") $ get_result_defs "vfmTestDefs1358";
val () = export_theory_no_docs ();
