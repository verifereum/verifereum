open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1849Theory;
val () = new_theory "vfmTest1849";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1849") $ get_result_defs "vfmTestDefs1849";
val () = export_theory_no_docs ();
