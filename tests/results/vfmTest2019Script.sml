open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2019Theory;
val () = new_theory "vfmTest2019";
val thyn = "vfmTestDefs2019";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
