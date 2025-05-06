open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2661Theory;
val () = new_theory "vfmTest2661";
val thyn = "vfmTestDefs2661";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
