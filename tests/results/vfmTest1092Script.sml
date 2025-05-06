open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1092Theory;
val () = new_theory "vfmTest1092";
val thyn = "vfmTestDefs1092";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
