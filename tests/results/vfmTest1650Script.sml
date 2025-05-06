open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1650Theory;
val () = new_theory "vfmTest1650";
val thyn = "vfmTestDefs1650";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
