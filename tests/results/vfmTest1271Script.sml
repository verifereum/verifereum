open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1271Theory;
val () = new_theory "vfmTest1271";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1271") $ get_result_defs "vfmTestDefs1271";
val () = export_theory_no_docs ();
