open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1855Theory;
val () = new_theory "vfmTest1855";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1855") $ get_result_defs "vfmTestDefs1855";
val () = export_theory_no_docs ();
