open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2853Theory;
val () = new_theory "vfmTest2853";
val thyn = "vfmTestDefs2853";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
