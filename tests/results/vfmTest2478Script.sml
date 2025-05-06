open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2478Theory;
val () = new_theory "vfmTest2478";
val thyn = "vfmTestDefs2478";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
