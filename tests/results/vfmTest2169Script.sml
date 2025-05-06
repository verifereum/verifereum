open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2169Theory;
val () = new_theory "vfmTest2169";
val thyn = "vfmTestDefs2169";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
