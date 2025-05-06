open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2499Theory;
val () = new_theory "vfmTest2499";
val thyn = "vfmTestDefs2499";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
