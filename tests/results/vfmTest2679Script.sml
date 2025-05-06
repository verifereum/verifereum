open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2679Theory;
val () = new_theory "vfmTest2679";
val thyn = "vfmTestDefs2679";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
