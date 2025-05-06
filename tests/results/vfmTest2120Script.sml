open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2120Theory;
val () = new_theory "vfmTest2120";
val thyn = "vfmTestDefs2120";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
