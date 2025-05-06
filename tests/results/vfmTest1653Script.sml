open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs1653Theory;
val () = new_theory "vfmTest1653";
val thyn = "vfmTestDefs1653";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
