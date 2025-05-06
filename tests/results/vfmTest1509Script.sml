open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1509Theory;
val () = new_theory "vfmTest1509";
val thyn = "vfmTestDefs1509";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
