open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0159Theory;
val () = new_theory "vfmTest0159";
val thyn = "vfmTestDefs0159";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
