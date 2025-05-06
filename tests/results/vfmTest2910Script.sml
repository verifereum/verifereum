open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2910Theory;
val () = new_theory "vfmTest2910";
val thyn = "vfmTestDefs2910";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
