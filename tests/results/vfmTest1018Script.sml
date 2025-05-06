open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1018Theory;
val () = new_theory "vfmTest1018";
val thyn = "vfmTestDefs1018";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
