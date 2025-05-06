open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1877Theory;
val () = new_theory "vfmTest1877";
val thyn = "vfmTestDefs1877";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
