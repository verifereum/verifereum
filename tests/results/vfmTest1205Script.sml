open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1205Theory;
val () = new_theory "vfmTest1205";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1205") $ get_result_defs "vfmTestDefs1205";
val () = export_theory_no_docs ();
