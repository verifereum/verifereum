open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1554Theory;
val () = new_theory "vfmTest1554";
val thyn = "vfmTestDefs1554";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
