open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2537Theory;
val () = new_theory "vfmTest2537";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2537") $ get_result_defs "vfmTestDefs2537";
val () = export_theory_no_docs ();
