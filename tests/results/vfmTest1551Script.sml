open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1551Theory;
val () = new_theory "vfmTest1551";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1551") $ get_result_defs "vfmTestDefs1551";
val () = export_theory_no_docs ();
