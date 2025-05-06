open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1896Theory;
val () = new_theory "vfmTest1896";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1896") $ get_result_defs "vfmTestDefs1896";
val () = export_theory_no_docs ();
