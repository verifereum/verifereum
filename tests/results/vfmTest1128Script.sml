open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1128Theory;
val () = new_theory "vfmTest1128";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1128") $ get_result_defs "vfmTestDefs1128";
val () = export_theory_no_docs ();
