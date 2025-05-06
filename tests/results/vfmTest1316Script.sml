open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1316Theory;
val () = new_theory "vfmTest1316";
val thyn = "vfmTestDefs1316";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
