open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2173Theory;
val () = new_theory "vfmTest2173";
val thyn = "vfmTestDefs2173";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
