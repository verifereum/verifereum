open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1849Theory;
val () = new_theory "vfmTest1849";
val thyn = "vfmTestDefs1849";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
