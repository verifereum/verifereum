open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1418Theory;
val () = new_theory "vfmTest1418";
val thyn = "vfmTestDefs1418";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
