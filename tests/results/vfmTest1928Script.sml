open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1928Theory;
val () = new_theory "vfmTest1928";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1928") $ get_result_defs "vfmTestDefs1928";
val () = export_theory_no_docs ();
