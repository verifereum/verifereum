open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2203Theory;
val () = new_theory "vfmTest2203";
val thyn = "vfmTestDefs2203";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
