open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1931Theory;
val () = new_theory "vfmTest1931";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1931") $ get_result_defs "vfmTestDefs1931";
val () = export_theory_no_docs ();
