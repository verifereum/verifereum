open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1591Theory;
val () = new_theory "vfmTest1591";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1591") $ get_result_defs "vfmTestDefs1591";
val () = export_theory_no_docs ();
