open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1338Theory;
val () = new_theory "vfmTest1338";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1338") $ get_result_defs "vfmTestDefs1338";
val () = export_theory_no_docs ();
