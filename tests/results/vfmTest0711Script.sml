open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0711Theory;
val () = new_theory "vfmTest0711";
val thyn = "vfmTestDefs0711";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
