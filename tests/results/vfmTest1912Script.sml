open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1912Theory;
val () = new_theory "vfmTest1912";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1912") $ get_result_defs "vfmTestDefs1912";
val () = export_theory_no_docs ();
