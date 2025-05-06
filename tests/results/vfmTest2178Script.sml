open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2178Theory;
val () = new_theory "vfmTest2178";
val thyn = "vfmTestDefs2178";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
