open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1059Theory;
val () = new_theory "vfmTest1059";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1059") $ get_result_defs "vfmTestDefs1059";
val () = export_theory_no_docs ();
