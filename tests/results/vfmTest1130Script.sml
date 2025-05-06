open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1130Theory;
val () = new_theory "vfmTest1130";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1130") $ get_result_defs "vfmTestDefs1130";
val () = export_theory_no_docs ();
