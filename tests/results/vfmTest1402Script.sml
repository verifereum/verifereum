open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1402Theory;
val () = new_theory "vfmTest1402";
val thyn = "vfmTestDefs1402";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
