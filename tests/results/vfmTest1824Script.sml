open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1824Theory;
val () = new_theory "vfmTest1824";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1824") $ get_result_defs "vfmTestDefs1824";
val () = export_theory_no_docs ();
