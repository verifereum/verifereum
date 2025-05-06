open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1769Theory;
val () = new_theory "vfmTest1769";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1769") $ get_result_defs "vfmTestDefs1769";
val () = export_theory_no_docs ();
