open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2003Theory;
val () = new_theory "vfmTest2003";
val thyn = "vfmTestDefs2003";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
