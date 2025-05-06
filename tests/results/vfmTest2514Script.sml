open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2514Theory;
val () = new_theory "vfmTest2514";
val thyn = "vfmTestDefs2514";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
