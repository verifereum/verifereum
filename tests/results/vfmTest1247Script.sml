open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1247Theory;
val () = new_theory "vfmTest1247";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1247") $ get_result_defs "vfmTestDefs1247";
val () = export_theory_no_docs ();
