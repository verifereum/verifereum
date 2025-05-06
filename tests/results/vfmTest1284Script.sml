open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1284Theory;
val () = new_theory "vfmTest1284";
val thyn = "vfmTestDefs1284";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
