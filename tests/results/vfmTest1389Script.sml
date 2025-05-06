open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1389Theory;
val () = new_theory "vfmTest1389";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1389") $ get_result_defs "vfmTestDefs1389";
val () = export_theory_no_docs ();
