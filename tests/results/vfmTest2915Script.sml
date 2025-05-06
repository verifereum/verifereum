open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs2915Theory;
val () = new_theory "vfmTest2915";
val thyn = "vfmTestDefs2915";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
