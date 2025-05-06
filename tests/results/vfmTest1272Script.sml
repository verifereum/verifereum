open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1272Theory;
val () = new_theory "vfmTest1272";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1272") $ get_result_defs "vfmTestDefs1272";
val () = export_theory_no_docs ();
