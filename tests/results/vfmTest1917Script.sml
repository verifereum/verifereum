open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1917Theory;
val () = new_theory "vfmTest1917";
val thyn = "vfmTestDefs1917";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
