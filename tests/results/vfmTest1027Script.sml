open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1027Theory;
val () = new_theory "vfmTest1027";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1027") $ get_result_defs "vfmTestDefs1027";
val () = export_theory_no_docs ();
