open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2705Theory;
val () = new_theory "vfmTest2705";
val thyn = "vfmTestDefs2705";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
