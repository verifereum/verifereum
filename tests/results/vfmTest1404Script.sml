open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1404Theory;
val () = new_theory "vfmTest1404";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1404") $ get_result_defs "vfmTestDefs1404";
val () = export_theory_no_docs ();
