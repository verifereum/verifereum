open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1733Theory;
val () = new_theory "vfmTest1733";
val thyn = "vfmTestDefs1733";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
