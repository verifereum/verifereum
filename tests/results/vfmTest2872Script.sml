open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2872Theory;
val () = new_theory "vfmTest2872";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2872") $ get_result_defs "vfmTestDefs2872";
val () = export_theory_no_docs ();
