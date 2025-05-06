open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1056Theory;
val () = new_theory "vfmTest1056";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1056") $ get_result_defs "vfmTestDefs1056";
val () = export_theory_no_docs ();
