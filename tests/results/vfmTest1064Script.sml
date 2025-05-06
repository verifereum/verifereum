open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1064Theory;
val () = new_theory "vfmTest1064";
val thyn = "vfmTestDefs1064";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
