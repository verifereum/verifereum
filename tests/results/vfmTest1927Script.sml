open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1927Theory;
val () = new_theory "vfmTest1927";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1927") $ get_result_defs "vfmTestDefs1927";
val () = export_theory_no_docs ();
