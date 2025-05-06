open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2866Theory;
val () = new_theory "vfmTest2866";
val thyn = "vfmTestDefs2866";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
