open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1795Theory;
val () = new_theory "vfmTest1795";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1795") $ get_result_defs "vfmTestDefs1795";
val () = export_theory_no_docs ();
