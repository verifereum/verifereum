open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2619Theory;
val () = new_theory "vfmTest2619";
val thyn = "vfmTestDefs2619";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
