open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1123Theory;
val () = new_theory "vfmTest1123";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1123") $ get_result_defs "vfmTestDefs1123";
val () = export_theory_no_docs ();
