open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1323Theory;
val () = new_theory "vfmTest1323";
val thyn = "vfmTestDefs1323";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
