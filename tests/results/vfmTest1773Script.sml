open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1773Theory;
val () = new_theory "vfmTest1773";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1773") $ get_result_defs "vfmTestDefs1773";
val () = export_theory_no_docs ();
