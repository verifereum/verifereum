open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2871Theory;
val () = new_theory "vfmTest2871";
val thyn = "vfmTestDefs2871";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
