open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2164Theory;
val () = new_theory "vfmTest2164";
val thyn = "vfmTestDefs2164";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
