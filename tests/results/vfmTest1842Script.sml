open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1842Theory;
val () = new_theory "vfmTest1842";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1842") $ get_result_defs "vfmTestDefs1842";
val () = export_theory_no_docs ();
