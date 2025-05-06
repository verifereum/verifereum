open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1337Theory;
val () = new_theory "vfmTest1337";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1337") $ get_result_defs "vfmTestDefs1337";
val () = export_theory_no_docs ();
