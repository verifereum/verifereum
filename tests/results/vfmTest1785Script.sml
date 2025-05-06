open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1785Theory;
val () = new_theory "vfmTest1785";
val thyn = "vfmTestDefs1785";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
