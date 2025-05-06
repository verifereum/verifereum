open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2440Theory;
val () = new_theory "vfmTest2440";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2440") $ get_result_defs "vfmTestDefs2440";
val () = export_theory_no_docs ();
