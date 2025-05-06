open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1103Theory;
val () = new_theory "vfmTest1103";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1103") $ get_result_defs "vfmTestDefs1103";
val () = export_theory_no_docs ();
