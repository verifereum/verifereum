open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1930Theory;
val () = new_theory "vfmTest1930";
val thyn = "vfmTestDefs1930";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
