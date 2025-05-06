open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2650Theory;
val () = new_theory "vfmTest2650";
val thyn = "vfmTestDefs2650";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
