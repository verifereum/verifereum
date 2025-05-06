open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0055Theory;
val () = new_theory "vfmTest0055";
val thyn = "vfmTestDefs0055";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
