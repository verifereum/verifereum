open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1442Theory;
val () = new_theory "vfmTest1442";
val thyn = "vfmTestDefs1442";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
