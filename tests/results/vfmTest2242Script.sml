open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2242Theory;
val () = new_theory "vfmTest2242";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2242") $ get_result_defs "vfmTestDefs2242";
val () = export_theory_no_docs ();
