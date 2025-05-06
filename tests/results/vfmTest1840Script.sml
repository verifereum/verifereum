open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1840Theory;
val () = new_theory "vfmTest1840";
val thyn = "vfmTestDefs1840";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
