open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2037Theory;
val () = new_theory "vfmTest2037";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2037") $ get_result_defs "vfmTestDefs2037";
val () = export_theory_no_docs ();
