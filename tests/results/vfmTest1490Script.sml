open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1490Theory;
val () = new_theory "vfmTest1490";
val thyn = "vfmTestDefs1490";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
