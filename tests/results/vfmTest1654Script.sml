open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1654Theory;
val () = new_theory "vfmTest1654";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1654") $ get_result_defs "vfmTestDefs1654";
val () = export_theory_no_docs ();
