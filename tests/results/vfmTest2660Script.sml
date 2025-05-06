open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2660Theory;
val () = new_theory "vfmTest2660";
val thyn = "vfmTestDefs2660";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
