open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2844Theory;
val () = new_theory "vfmTest2844";
val thyn = "vfmTestDefs2844";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
