open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1092Theory;
val () = new_theory "vfmTest1092";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1092") $ get_result_defs "vfmTestDefs1092";
val () = export_theory_no_docs ();
