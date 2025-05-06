open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2707Theory;
val () = new_theory "vfmTest2707";
val thyn = "vfmTestDefs2707";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
