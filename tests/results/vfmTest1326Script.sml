open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1326Theory;
val () = new_theory "vfmTest1326";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1326") $ get_result_defs "vfmTestDefs1326";
val () = export_theory_no_docs ();
