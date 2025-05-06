open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2510Theory;
val () = new_theory "vfmTest2510";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2510") $ get_result_defs "vfmTestDefs2510";
val () = export_theory_no_docs ();
