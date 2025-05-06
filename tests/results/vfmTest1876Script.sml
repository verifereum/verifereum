open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1876Theory;
val () = new_theory "vfmTest1876";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1876") $ get_result_defs "vfmTestDefs1876";
val () = export_theory_no_docs ();
