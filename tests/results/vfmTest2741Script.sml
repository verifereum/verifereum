open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2741Theory;
val () = new_theory "vfmTest2741";
val thyn = "vfmTestDefs2741";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
