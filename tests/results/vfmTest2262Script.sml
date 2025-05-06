open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2262Theory;
val () = new_theory "vfmTest2262";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2262") $ get_result_defs "vfmTestDefs2262";
val () = export_theory_no_docs ();
