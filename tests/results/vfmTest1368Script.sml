open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1368Theory;
val () = new_theory "vfmTest1368";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1368") $ get_result_defs "vfmTestDefs1368";
val () = export_theory_no_docs ();
