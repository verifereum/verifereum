open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0636Theory;
val () = new_theory "vfmTest0636";
val thyn = "vfmTestDefs0636";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
