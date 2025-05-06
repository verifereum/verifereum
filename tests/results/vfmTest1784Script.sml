open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1784Theory;
val () = new_theory "vfmTest1784";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1784") $ get_result_defs "vfmTestDefs1784";
val () = export_theory_no_docs ();
