open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1915Theory;
val () = new_theory "vfmTest1915";
val thyn = "vfmTestDefs1915";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
