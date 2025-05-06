open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1753Theory;
val () = new_theory "vfmTest1753";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1753") $ get_result_defs "vfmTestDefs1753";
val () = export_theory_no_docs ();
