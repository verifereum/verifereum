open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1609Theory;
val () = new_theory "vfmTest1609";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1609") $ get_result_defs "vfmTestDefs1609";
val () = export_theory_no_docs ();
