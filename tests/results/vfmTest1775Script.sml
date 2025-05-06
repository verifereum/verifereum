open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1775Theory;
val () = new_theory "vfmTest1775";
val thyn = "vfmTestDefs1775";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
