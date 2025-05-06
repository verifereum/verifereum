open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2083Theory;
val () = new_theory "vfmTest2083";
val thyn = "vfmTestDefs2083";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
