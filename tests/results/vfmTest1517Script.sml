open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1517Theory;
val () = new_theory "vfmTest1517";
val thyn = "vfmTestDefs1517";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
