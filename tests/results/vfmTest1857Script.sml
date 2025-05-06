open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1857Theory;
val () = new_theory "vfmTest1857";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1857") $ get_result_defs "vfmTestDefs1857";
val () = export_theory_no_docs ();
