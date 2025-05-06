open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1297Theory;
val () = new_theory "vfmTest1297";
val thyn = "vfmTestDefs1297";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
