open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2873Theory;
val () = new_theory "vfmTest2873";
val thyn = "vfmTestDefs2873";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
