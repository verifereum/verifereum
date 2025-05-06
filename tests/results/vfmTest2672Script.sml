open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2672Theory;
val () = new_theory "vfmTest2672";
val thyn = "vfmTestDefs2672";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
