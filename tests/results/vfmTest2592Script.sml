open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2592Theory;
val () = new_theory "vfmTest2592";
val thyn = "vfmTestDefs2592";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
