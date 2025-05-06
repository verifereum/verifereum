open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2091Theory;
val () = new_theory "vfmTest2091";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2091") $ get_result_defs "vfmTestDefs2091";
val () = export_theory_no_docs ();
