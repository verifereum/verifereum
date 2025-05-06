open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2602Theory;
val () = new_theory "vfmTest2602";
val thyn = "vfmTestDefs2602";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
