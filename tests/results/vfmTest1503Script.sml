open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1503Theory;
val () = new_theory "vfmTest1503";
val thyn = "vfmTestDefs1503";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
