open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0272Theory;
val () = new_theory "vfmTest0272";
val thyn = "vfmTestDefs0272";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
