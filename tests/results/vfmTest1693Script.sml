open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1693Theory;
val () = new_theory "vfmTest1693";
val thyn = "vfmTestDefs1693";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
