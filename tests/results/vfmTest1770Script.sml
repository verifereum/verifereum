open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1770Theory;
val () = new_theory "vfmTest1770";
val thyn = "vfmTestDefs1770";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
