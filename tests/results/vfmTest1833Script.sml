open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1833Theory;
val () = new_theory "vfmTest1833";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1833") $ get_result_defs "vfmTestDefs1833";
val () = export_theory_no_docs ();
