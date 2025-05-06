open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2918Theory;
val () = new_theory "vfmTest2918";
val thyn = "vfmTestDefs2918";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
