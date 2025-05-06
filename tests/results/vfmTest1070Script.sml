open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1070Theory;
val () = new_theory "vfmTest1070";
val thyn = "vfmTestDefs1070";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
