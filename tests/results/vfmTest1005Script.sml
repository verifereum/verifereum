open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1005Theory;
val () = new_theory "vfmTest1005";
val thyn = "vfmTestDefs1005";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
