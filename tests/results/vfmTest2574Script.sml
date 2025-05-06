open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2574Theory;
val () = new_theory "vfmTest2574";
val thyn = "vfmTestDefs2574";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
