open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0213Theory;
val () = new_theory "vfmTest0213";
val thyn = "vfmTestDefs0213";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
