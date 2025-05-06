open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2204Theory;
val () = new_theory "vfmTest2204";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2204") $ get_result_defs "vfmTestDefs2204";
val () = export_theory_no_docs ();
