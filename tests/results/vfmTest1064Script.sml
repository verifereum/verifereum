open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1064Theory;
val () = new_theory "vfmTest1064";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1064") $ get_result_defs "vfmTestDefs1064";
val () = export_theory_no_docs ();
