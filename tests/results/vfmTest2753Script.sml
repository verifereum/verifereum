open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2753Theory;
val () = new_theory "vfmTest2753";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2753") $ get_result_defs "vfmTestDefs2753";
val () = export_theory_no_docs ();
