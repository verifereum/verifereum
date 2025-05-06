open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1396Theory;
val () = new_theory "vfmTest1396";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1396") $ get_result_defs "vfmTestDefs1396";
val () = export_theory_no_docs ();
