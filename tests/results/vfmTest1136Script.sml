open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1136Theory;
val () = new_theory "vfmTest1136";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1136") $ get_result_defs "vfmTestDefs1136";
val () = export_theory_no_docs ();
