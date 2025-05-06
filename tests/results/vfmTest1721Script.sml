open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1721Theory;
val () = new_theory "vfmTest1721";
val thyn = "vfmTestDefs1721";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
