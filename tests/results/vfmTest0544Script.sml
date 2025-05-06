open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0544Theory;
val () = new_theory "vfmTest0544";
val thyn = "vfmTestDefs0544";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
