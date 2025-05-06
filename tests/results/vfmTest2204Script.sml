open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2204Theory;
val () = new_theory "vfmTest2204";
val thyn = "vfmTestDefs2204";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
