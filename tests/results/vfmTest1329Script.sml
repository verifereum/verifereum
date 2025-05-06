open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1329Theory;
val () = new_theory "vfmTest1329";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1329") $ get_result_defs "vfmTestDefs1329";
val () = export_theory_no_docs ();
