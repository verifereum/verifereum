open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1856Theory;
val () = new_theory "vfmTest1856";
val thyn = "vfmTestDefs1856";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
