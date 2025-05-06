open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2133Theory;
val () = new_theory "vfmTest2133";
val thyn = "vfmTestDefs2133";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
