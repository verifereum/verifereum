open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0620Theory;
val () = new_theory "vfmTest0620";
val thyn = "vfmTestDefs0620";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
