open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1878Theory;
val () = new_theory "vfmTest1878";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1878") $ get_result_defs "vfmTestDefs1878";
val () = export_theory_no_docs ();
