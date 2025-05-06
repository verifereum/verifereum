open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1740Theory;
val () = new_theory "vfmTest1740";
val thyn = "vfmTestDefs1740";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
