open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0492Theory;
val () = new_theory "vfmTest0492";
val thyn = "vfmTestDefs0492";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
