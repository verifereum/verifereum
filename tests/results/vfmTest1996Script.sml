open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1996Theory;
val () = new_theory "vfmTest1996";
val thyn = "vfmTestDefs1996";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
