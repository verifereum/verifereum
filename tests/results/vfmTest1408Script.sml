open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1408Theory;
val () = new_theory "vfmTest1408";
val thyn = "vfmTestDefs1408";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
