open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1801Theory;
val () = new_theory "vfmTest1801";
val thyn = "vfmTestDefs1801";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
