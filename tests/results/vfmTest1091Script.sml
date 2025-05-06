open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1091Theory;
val () = new_theory "vfmTest1091";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1091") $ get_result_defs "vfmTestDefs1091";
val () = export_theory_no_docs ();
