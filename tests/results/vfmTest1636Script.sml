open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1636Theory;
val () = new_theory "vfmTest1636";
val thyn = "vfmTestDefs1636";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
