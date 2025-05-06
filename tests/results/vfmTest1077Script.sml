open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1077Theory;
val () = new_theory "vfmTest1077";
val thyn = "vfmTestDefs1077";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
