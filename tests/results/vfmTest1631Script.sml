open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1631Theory;
val () = new_theory "vfmTest1631";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1631") $ get_result_defs "vfmTestDefs1631";
val () = export_theory_no_docs ();
