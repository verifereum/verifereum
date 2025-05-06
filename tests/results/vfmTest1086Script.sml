open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1086Theory;
val () = new_theory "vfmTest1086";
val thyn = "vfmTestDefs1086";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
