open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2337Theory;
val () = new_theory "vfmTest2337";
val thyn = "vfmTestDefs2337";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
