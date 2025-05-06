open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0617Theory;
val () = new_theory "vfmTest0617";
val thyn = "vfmTestDefs0617";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
