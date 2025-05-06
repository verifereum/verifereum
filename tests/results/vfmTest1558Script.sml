open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1558Theory;
val () = new_theory "vfmTest1558";
val thyn = "vfmTestDefs1558";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
