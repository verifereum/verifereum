open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0728Theory;
val () = new_theory "vfmTest0728";
val thyn = "vfmTestDefs0728";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
