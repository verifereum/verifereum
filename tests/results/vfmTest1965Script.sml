open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1965Theory;
val () = new_theory "vfmTest1965";
val thyn = "vfmTestDefs1965";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
