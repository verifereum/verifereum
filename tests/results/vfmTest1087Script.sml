open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1087Theory;
val () = new_theory "vfmTest1087";
val thyn = "vfmTestDefs1087";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
