open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2527Theory;
val () = new_theory "vfmTest2527";
val thyn = "vfmTestDefs2527";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
