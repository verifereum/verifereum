open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1498Theory;
val () = new_theory "vfmTest1498";
val thyn = "vfmTestDefs1498";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
