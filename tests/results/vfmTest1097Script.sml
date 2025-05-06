open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1097Theory;
val () = new_theory "vfmTest1097";
val thyn = "vfmTestDefs1097";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
