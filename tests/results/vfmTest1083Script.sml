open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1083Theory;
val () = new_theory "vfmTest1083";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1083") $ get_result_defs "vfmTestDefs1083";
val () = export_theory_no_docs ();
