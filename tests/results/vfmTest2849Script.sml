open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2849Theory;
val () = new_theory "vfmTest2849";
val thyn = "vfmTestDefs2849";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
