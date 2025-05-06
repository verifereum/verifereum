open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2158Theory;
val () = new_theory "vfmTest2158";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2158") $ get_result_defs "vfmTestDefs2158";
val () = export_theory_no_docs ();
