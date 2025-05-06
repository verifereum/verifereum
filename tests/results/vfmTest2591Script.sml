open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2591Theory;
val () = new_theory "vfmTest2591";
val thyn = "vfmTestDefs2591";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
